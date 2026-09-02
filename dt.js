/* ===========================================================================
   dt.js - the Drawthing runtime.

   The shared half of the editor (index.html) and the game (game.html). It is a
   CLASSIC script that assigns to window.DT, deliberately not an ES module: the
   editor's whole test methodology drives it through javascript_exec reaching
   top-level names, and module scope would hide every one of them. It is loaded
   BEFORE both the supabase module script and the app script, because the app
   builds its document handle at top level and needs DT to exist by then.

   Nothing in here may:
     - touch the DOM, or reach for a canvas of its own (every painter takes its
       2d context `g` as an argument),
     - call requestAnimationFrame. There is exactly ONE animation loop and it
       lives in the app; a scheduler in here would be a second one.
     - hold per-document state in a module-level variable. That is the whole
       reason this file exists: the game draws MANY documents in one frame, so
       every cache is keyed on, or lives on, the document it belongs to.

   The editor keeps its own top-level globals and reaches these through
   one-line forwarders of the identical signature, so its ~50 existing call
   sites and every test in CLAUDE.md are untouched.
   =========================================================================== */
(function (root) {
  'use strict';
  const DT = {};

  /* Stamped so a test can tell a reloaded page from a cached one - `-c-1`
     disables caching, but a stale dt.js reads as a baffling failure. */
  DT.BUILD = '1.5.0';

  /* ------------------------------------------------------------- constants */
  const TAU = Math.PI * 2;
  /* A colour slot holding NONE means "do not render this part at all". It is
     part of the saved scene format, so it is a value, not a preference. */
  const NONE = 'none';
  /* The colour the canvas is filled with. An outline this colour is invisible
     for exactly as long as it is being drawn, which is when you need to see it;
     `lowContrast` is what the live stroke tests to decide to invert instead. */
  const PAPER_RGB = [0xF7, 0xF4, 0xEE];

  /* Two colours only. TERMINATOR is where the light stops, SOFTNESS how
     abruptly - small keeps the falloff crisp instead of smearing midtones. */
  const TERMINATOR = 0.62;
  const SOFTNESS = 0.04;
  /* The only curvature control: small = tightly curved and wraps round the
     side, large = flattens to a line. It changes the curve and NOT the tone,
     because the arc is made to pass through the point the straight cut would. */
  const LIGHT_DIST = 0.7;

  /* Default light axis, as two corners of the shape's box in 0..1 fractions:
     lit corner -> dark corner. A document may carry its own pair. */
  const LIGHT_FROM = { x: 1, y: 0 };   // top right
  const LIGHT_TO = { x: 0, y: 1 };     // bottom left

  /* -------------------------------------------------------------- geometry */
  const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
  const mid = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 });

  function toWorld(s, p) {
    const x = p.x * s.sx, y = p.y * s.sy, c = Math.cos(s.rot), n = Math.sin(s.rot);
    return { x: s.x + x * c - y * n, y: s.y + x * n + y * c };
  }
  function toLocal(s, w) {
    const dx = w.x - s.x, dy = w.y - s.y, c = Math.cos(-s.rot), n = Math.sin(-s.rot);
    return { x: (dx * c - dy * n) / s.sx, y: (dx * n + dy * c) / s.sy };
  }

  function bbox(pts) {
    let a = 1e9, b = 1e9, c = -1e9, d = -1e9;
    for (const p of pts) { if (p.x < a) a = p.x; if (p.y < b) b = p.y; if (p.x > c) c = p.x; if (p.y > d) d = p.y; }
    return { x0: a, y0: b, x1: c, y1: d, w: c - a, h: d - b, cx: (a + c) / 2, cy: (b + d) / 2 };
  }

  function pathLength(pts) {
    let L = 0; for (let i = 1; i < pts.length; i++) L += dist(pts[i - 1], pts[i]);
    return L;
  }

  function segDist(p, a, b) {
    const vx = b.x - a.x, vy = b.y - a.y, L = vx * vx + vy * vy;
    let t = L ? ((p.x - a.x) * vx + (p.y - a.y) * vy) / L : 0;
    t = t < 0 ? 0 : t > 1 ? 1 : t;
    return Math.hypot(p.x - (a.x + vx * t), p.y - (a.y + vy * t));
  }

  function segCross(a, b, c, d) {
    const rx = b.x - a.x, ry = b.y - a.y, sx2 = d.x - c.x, sy2 = d.y - c.y;
    const den = rx * sy2 - ry * sx2;
    if (Math.abs(den) < 1e-9) return null;
    const t = ((c.x - a.x) * sy2 - (c.y - a.y) * sx2) / den;
    const u = ((c.x - a.x) * ry - (c.y - a.y) * rx) / den;
    if (t <= 0 || t >= 1 || u <= 0 || u >= 1) return null;
    return { x: a.x + rx * t, y: a.y + ry * t };
  }

  /* The 16-point placement box a reference is drawn in. buildPath is a
     quadratic through segment MIDPOINTS, so four corners would draw as a
     squircle inscribed in the rectangle - each edge is subdivided into four so
     the corners of an imported drawing stay clickable. */
  function boxPts(w, h) {
    const hx = w / 2, hy = h / 2, N = 4, out = [];
    const c = [{ x: -hx, y: -hy }, { x: hx, y: -hy }, { x: hx, y: hy }, { x: -hx, y: hy }];
    for (let i = 0; i < 4; i++) {
      const a = c[i], d = c[(i + 1) % 4];
      for (let j = 0; j < N; j++) out.push({ x: a.x + (d.x - a.x) * j / N, y: a.y + (d.y - a.y) * j / N });
    }
    return out;
  }

  /* -------------------------------------------------------- path builders */
  /* Smooth closed path through points (quadratics via segment midpoints).
     This is the single biggest "makes a wobbly hand look competent" trick.
     The FILL always uses this, closed or not - that is what lets an open
     stroke still hold colour. */
  function buildPath(g, pts) {
    const n = pts.length;
    g.beginPath();
    if (n < 3) { if (n) g.moveTo(pts[0].x, pts[0].y); for (let i = 1; i < n; i++) g.lineTo(pts[i].x, pts[i].y); return; }
    const m0 = mid(pts[n - 1], pts[0]);
    g.moveTo(m0.x, m0.y);
    for (let i = 0; i < n; i++) {
      const p = pts[i], q = pts[(i + 1) % n], m = mid(p, q);
      g.quadraticCurveTo(p.x, p.y, m.x, m.y);
    }
    g.closePath();
  }

  /* The region a shape fills. For an open stroke the chord is a dead-straight
     line between the two endpoints, so the bare edge really is flat and the
     outline stops exactly on it instead of overshooting into whiskers. */
  function buildFill(g, pts, closed) {
    if (closed) buildPath(g, pts);
    else { buildOpenPath(g, pts); g.closePath(); }
  }

  /* Same curve, but only across the part the user actually drew - the closing
     chord is left bare so shapes can be layered against a clean edge. */
  function buildOpenPath(g, pts) {
    const n = pts.length;
    g.beginPath();
    if (n < 3) { if (n) g.moveTo(pts[0].x, pts[0].y); for (let i = 1; i < n; i++) g.lineTo(pts[i].x, pts[i].y); return; }
    g.moveTo(pts[0].x, pts[0].y);
    for (let i = 1; i < n - 1; i++) {
      const m = mid(pts[i], pts[i + 1]);
      g.quadraticCurveTo(pts[i].x, pts[i].y, m.x, m.y);
    }
    g.lineTo(pts[n - 1].x, pts[n - 1].y);
  }

  /* ------------------------------------------------------- simplification */
  /* Ramer-Douglas-Peucker */
  function rdp(pts, eps) {
    if (pts.length < 3) return pts.slice();
    const keep = new Array(pts.length).fill(false);
    keep[0] = keep[pts.length - 1] = true;
    (function rec(a, b) {
      let idx = -1, max = 0;
      const A = pts[a], B = pts[b], dx = B.x - A.x, dy = B.y - A.y, len = Math.hypot(dx, dy) || 1;
      for (let i = a + 1; i < b; i++) {
        const d = Math.abs((pts[i].x - A.x) * dy - (pts[i].y - A.y) * dx) / len;
        if (d > max) { max = d; idx = i; }
      }
      if (max > eps && idx > 0) { keep[idx] = true; rec(a, idx); rec(idx, b); }
    })(0, pts.length - 1);
    return pts.filter((_, i) => keep[i]);
  }

  /* RDP measures every point against the chord from the FIRST point to the LAST.
     On a CLOSED loop those two are neighbours, so that baseline is degenerate and
     what survives depends on where the stroke happened to start: the same thin
     sliver kept anywhere from 77% to 94% of its area depending only on the seam,
     which is what made thin shapes collapse unpredictably rather than always.
     So split the loop at its two most distant points and simplify the halves as
     open runs - the baseline is then the shape's own long axis every time. The
     pair is the usual two-pass approximation of the diameter (furthest from any
     point, then furthest from that), so it does not depend on the seam either. */
  function rdpLoop(pts, eps) {
    const n = pts.length; if (n < 6) return rdp(pts, eps);
    const farFrom = i => {
      let k = i, best = -1;
      for (let j = 0; j < n; j++) { const d = dist(pts[i], pts[j]); if (d > best) { best = d; k = j; } } return k;
    };
    let a = farFrom(farFrom(0)), b = farFrom(a);
    if (a > b) { const t = a; a = b; b = t; }
    // Degenerate split (the two ends adjacent) leaves nothing to simplify.
    if (b - a < 2 || n - (b - a) < 2) return rdp(pts, eps);
    const A = rdp(pts.slice(a, b + 1), eps);                      // a -> b
    const B = rdp(pts.slice(b).concat(pts.slice(0, a + 1)), eps); // b -> a, round the seam
    return A.slice(0, -1).concat(B.slice(0, -1));                 // drop the shared ends
  }

  /* Even spacing => predictable dots to drag and clean deformation.
     Open shapes are resampled along the drawn run only, keeping both
     endpoints exact - no points are invented along the closing chord. */
  function resample(pts, step, closed) {
    const n = pts.length; if (n < 3) return pts.slice();
    const out = []; let carry = 0;
    const last = closed ? n : n - 1;
    for (let i = 0; i < last; i++) {
      const a = pts[i], b = pts[(i + 1) % n];
      const seg = dist(a, b); if (seg < 1e-6) continue;
      let t = carry;
      while (t < seg) { out.push({ x: a.x + (b.x - a.x) * t / seg, y: a.y + (b.y - a.y) * t / seg }); t += step; }
      carry = t - seg;
    }
    if (!closed) out.push({ x: pts[n - 1].x, y: pts[n - 1].y });
    return out.length >= 3 ? out : pts.slice();
  }

  function arcLengths(pts, closed) {
    const n = pts.length, s = new Array(n); let acc = 0;
    for (let i = 0; i < n; i++) {
      s[i] = acc;
      if (closed || i < n - 1) acc += dist(pts[i], pts[(i + 1) % n]);
    }
    return { s, total: acc || 1 };
  }

  function laplacian(pts, amount, passes, closed) {
    let p = pts.map(q => ({ x: q.x, y: q.y }));
    for (let k = 0; k < passes; k++) {
      const n = p.length, out = p.map(q => ({ x: q.x, y: q.y }));
      for (let i = 0; i < n; i++) {
        if (!closed && (i === 0 || i === n - 1)) continue;   // endpoints of an open run stay put
        const a = p[(i - 1 + n) % n], b = p[(i + 1) % n];
        out[i] = {
          x: p[i].x + ((a.x + b.x) / 2 - p[i].x) * amount,
          y: p[i].y + ((a.y + b.y) / 2 - p[i].y) * amount
        };
      }
      p = out;
    }
    return p;
  }

  /* --------------------------------------------------------------- colours */
  function hex2rgb(h) {
    h = h.replace('#', '');
    if (h.length === 3) h = h.split('').map(c => c + c).join('');
    return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16)];
  }
  const clamp255 = v => Math.max(0, Math.min(255, Math.round(v)));
  function shade(hex, amt) { // amt>0 lighten, amt<0 darken
    const [r, g, b] = hex2rgb(hex);
    const f = v => amt > 0 ? v + (255 - v) * amt : v * (1 + amt);
    return 'rgb(' + clamp255(f(r)) + ',' + clamp255(f(g)) + ',' + clamp255(f(b)) + ')';
  }
  /* Like hex2rgb but total: returns null rather than NaNs for anything that is
     not a hex colour, which is what lets lowContrast take NONE and rgb() too. */
  function hexRGB(c) {
    if (typeof c !== 'string') return null;
    let h = c.trim().replace('#', '');
    if (h.length === 3) h = h[0] + h[0] + h[1] + h[1] + h[2] + h[2];
    if (!/^[0-9a-fA-F]{6}$/.test(h)) return null;
    return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16)];
  }
  function lowContrast(c) {
    if (c === NONE) return true;
    const a = hexRGB(c);
    if (!a) return false;
    return Math.abs(a[0] - PAPER_RGB[0]) + Math.abs(a[1] - PAPER_RGB[1]) + Math.abs(a[2] - PAPER_RGB[2]) < 96;
  }

  /* ----------------------------------------------------------------- light */
  /* `from`/`to` are the axis corners in 0..1 fractions. They were two module
     globals in the editor; a document carries its own pair now, because the
     game may draw two documents lit differently in one frame. Both default to
     the module pair, so an editor call with one argument is unchanged. */
  function lightAxis(b, from, to) {
    const F = from || LIGHT_FROM, T = to || LIGHT_TO;
    const A = { x: b.x0 + F.x * b.w, y: b.y0 + F.y * b.h };
    const B = { x: b.x0 + T.x * b.w, y: b.y0 + T.y * b.h };
    const dx = B.x - A.x, dy = B.y - A.y, L = Math.hypot(dx, dy) || 1;
    return { A: A, B: B, d: { x: dx / L, y: dy / L }, L: L };
  }

  /* The terminator is an ARC, not a straight cut - a curved edge is what reads
     as a rounded form. The light is a point sitting off the lit side, back
     along the axis. Wherever it sits, the arc is made to pass through the same
     point the straight version would have cut, which is what keeps LIGHT_DIST
     (curvature) and TERMINATOR (how much is shadowed) independent. Preserve
     that property if you touch this. */
  function terminatorArc(b, from, to) {
    const ax = lightAxis(b, from, to);
    const diag = Math.hypot(b.w, b.h) || 1;
    const L = { x: b.cx - ax.d.x * diag * LIGHT_DIST, y: b.cy - ax.d.y * diag * LIGHT_DIST };
    const Q = { x: ax.A.x + ax.d.x * ax.L * TERMINATOR, y: ax.A.y + ax.d.y * ax.L * TERMINATOR };
    return { L: L, R: dist(L, Q) };
  }

  /* ============================================================ the Doc
     A Doc is one drawing: its content, its cursor into that content, its
     skeleton, its references, and - critically - ITS OWN CACHES.

     The editor has exactly one and it is built by bindDoc over the editor s own
     top-level globals, so those globals stay the authority and code that
     REASSIGNS rig / restPose / bonePose / anims wholesale (restore, applyAnim,
     sceneFromJSON) keeps working with nothing to sync. The game has one per
     distinct drawing plus a light instanceOf per actor.

     Caches are ALWAYS own data properties, never accessors: they belong to the
     Doc, not to whatever the Doc is a view onto. */
  function newDoc(init) {
    return Object.assign({
      // identity
      id: null, title: null, rev: 0, kind: 'character',
      // content
      views: {}, viewNames: [], frameNames: null, anims: [], animIdx: 0,
      // cursor
      view: 'front', frame: 0,
      // rig. The hierarchy is one per document, the rest is per VIEW, and the
      // pose is one delta per FRAME of the current animation.
      rig: [], restPose: {}, bonePose: [],
      // imported drawings, keyed `drawingId@rev`
      refLib: new Map(),
      // the only three render settings a document actually varies
      shading: 'hatch', lightFrom: DT.LIGHT_FROM, lightTo: DT.LIGHT_TO,
      // cache generations: rigRev is bumped by a POSE change too, bindRev only
      // by a structure or rest change, because weights are measured against the
      // bind and keying them on rigRev would throw them away 60 times a second.
      rigRev: 0, bindRev: 0,
      /* the D-matrix cache. This was ONE global slot keyed (frame,view,rigRev)
         with no document identity: two characters in a single tick thrashed it,
         and a key collision across two documents silently returned the wrong
         one s matrices. Per-doc and a small Map, so one document at several
         frames in one tick - a crowd walking out of phase - also hits. */
      _mats: new Map(), _matQ: [], _skin: new WeakMap()
    }, init);
  }

  /* Redefine named fields as live GETTERS over the caller s own bindings. A
     getter reads its binding at call time, which is the whole trick: the editor
     may reassign `rig` wholesale and this Doc sees the new array on the next
     read, with no sync step and nothing to forget. */
  function bindDoc(d, map) {
    for (const k of Object.keys(map))
      Object.defineProperty(d, k, { get: map[k], configurable: true, enumerable: true });
    return d;
  }

  const bumpRig  = d => { d.rigRev++; };
  const bumpBind = d => { d.bindRev++; d.rigRev++; };

  /* ====================================================== rig and skinning
     Every one of these took `rig` / `restPose` / `bonePose` / `view` / `frame`
     off the module scope. They take a Doc now, and that is the whole of what
     lets the game draw two characters, at two frames, in one tick. */

  const REST0 = { len: 0, rot: 0, att: 1, off: 0, mx: 1, my: 1 };

  /* restAt is to restPose what cur() is to views and poseAt is to bonePose: the
     render loop is always in flight and must never read undefined out of one.
     The lazy write is a MUTATION of doc.restPose, not a rebind, which is why an
     accessor-backed Doc needs no setter for it. */
  const restAt = (doc, v) => { const k = v || doc.view; return doc.restPose[k] || (doc.restPose[k] = {}); };
  const restBone = (doc, id, v) => restAt(doc, v)[id] || REST0;
  const poseAt = (doc, f) => doc.bonePose[f] || {};

  // the rotation sense: a reflected rest swings the other way for the same delta
  const mirOf = r => (r.mx == null ? 1 : r.mx) * (r.my == null ? 1 : r.my);
  const sgnX = r => (r.mx < 0 ? -1 : 1);
  const sgnY = r => (r.my < 0 ? -1 : 1);

  const boneById = (doc, id) => { for (const b of doc.rig) if (b.id === id) return b; return null; };

  /* One forward pass down `rig`, which is why parents must precede children -
     addBone always pushes to the END, and a bone's parent is by definition
     already in the array, so a push can never break it.
     boneWorld(doc, {}, v) is therefore that view's REST skeleton. */
  function boneWorld(doc, pose, v) {
    const R = restAt(doc, v), M = new Map(), rig = doc.rig;
    for (const b of rig) {
      const r = R[b.id] || REST0, d = pose[b.id] || null;
      const lrot = (r.rot || 0) + mirOf(r) * ((d && d.drot) || 0);
      const len = (r.len || 0) * ((d && d.klen != null) ? d.klen : 1);
      let x, y, rot;
      const pw = b.parent != null ? M.get(b.parent) : null;
      if (!pw) {                                     // root, or an orphan treated as one
        x = (r.x || 0) + sgnX(r) * ((d && d.dx) || 0);
        y = (r.y || 0) + sgnY(r) * ((d && d.dy) || 0);
        rot = lrot;
      }
      else {
        // along the parent, then perpendicular to it, both in the parent's frame
        const t = (r.att == null ? 1 : r.att) * pw.len, o = r.off || 0;
        const c = Math.cos(pw.rot), n = Math.sin(pw.rot);
        x = pw.x + c * t - n * o; y = pw.y + n * t + c * o;
        rot = pw.rot + lrot;
      }
      M.set(b.id, { x: x, y: y, rot: rot, len: len });
    }
    return M;
  }
  const boneTip = w => ({ x: w.x + Math.cos(w.rot) * w.len, y: w.y + Math.sin(w.rot) * w.len });
  /* Where a child hanging off `att` of this bone starts. */
  const boneAt = (w, t) => ({ x: w.x + Math.cos(w.rot) * w.len * t, y: w.y + Math.sin(w.rot) * w.len * t });

  const SKIN_EPS = 1.5;      // a point sitting exactly on a bone must not divide by zero
  const SKIN_MAXB = 2;       // influences kept per point
  const MIN_BONE_K = 0.06;   // toLocal divides by sx/sy; a zero-length bone would NaN everything
  const MATS_CAP = 8;        // see skinMats

  function skinOf(doc, s) {
    if (!s || !s.skin || !s.skin.bones || !s.skin.bones.length) return null;
    const bs = s.skin.bones.filter(id => boneById(doc, id) != null);
    if (!bs.length) return null;                 // dangling ids read as unbound
    return { bones: bs, falloff: s.skin.falloff || 0 };
  }

  /* D = M_pose . M_bind^-1 per bone, as a similarity:
        D(p) = o_pose + k . R(dtheta) . (p - o_bind)
     Computed ONCE per drawn frame - never per shape, which is the difference
     between this costing nothing and costing the render loop. The view is in
     the key because the rest skeleton the bind half comes from is per view.

     The cache lives ON THE DOC. It used to be one module-level slot keyed
     (frame, view, rigRev) with no document identity at all: two characters in
     a single tick thrashed it, and - worse - two documents colliding on that
     tuple silently got each other's matrices. A small per-doc Map also means
     one document drawn at several frames in one tick (a crowd walking out of
     phase) hits instead of missing every time. Capped so it cannot grow with
     the frame count.

     f < 0 (REST_F) means "no deformation at all": the pose is a delta from the
     rest, so an empty pose IS the rest and every D comes out the identity. That
     is what Add Bones and Edit Bones draw against. */
  function skinMats(doc, f, v) {
    v = v || doc.view;
    const key = f + ':' + v + ':' + doc.rigRev;
    const hit = doc._mats.get(key);
    if (hit) return hit;
    const B = boneWorld(doc, {}, v), P = boneWorld(doc, f < 0 ? {} : poseAt(doc, f), v);
    const M = new Map();
    for (const b of doc.rig) {
      const ob = B.get(b.id), op = P.get(b.id);
      if (!ob || !op) continue;
      const k = ob.len > 0.0001 ? Math.max(MIN_BONE_K, op.len / ob.len) : 1;
      const d = op.rot - ob.rot, c = Math.cos(d), n = Math.sin(d);
      M.set(b.id, {
        c: c, n: n, k: k,
        tx: op.x - k * (c * ob.x - n * ob.y),
        ty: op.y - k * (n * ob.x + c * ob.y),
        // at rest this is the identity and worldPts can return the raw points
        id: Math.abs(d) < 1e-12 && Math.abs(k - 1) < 1e-12 &&
          Math.abs(op.x - ob.x) < 1e-9 && Math.abs(op.y - ob.y) < 1e-9
      });
    }
    doc._mats.set(key, M); doc._matQ.push(key);
    while (doc._matQ.length > MATS_CAP) doc._mats.delete(doc._matQ.shift());
    return M;
  }
  const applyD = (D, p) => ({
    x: D.k * (D.c * p.x - D.n * p.y) + D.tx,
    y: D.k * (D.n * p.x + D.c * p.y) + D.ty
  });

  /* Weights depend on the BIND pose and on the rig's structure, never on the
     current pose - so they are keyed on bindRev and survive a whole drag. Held
     in a WeakMap rather than on the shape: a field would be carried straight
     into sceneToJSON's stringify and into every undo snapshot. The WeakMap is
     the Doc's, because bindRev is. */
  function skinWeights(doc, s, v) {
    const sk = skinOf(doc, s);
    if (!sk) return null;
    v = v || doc.view;
    // the view is in the key too: the rest they are measured against is per view
    const key = v + ':' + doc.bindRev + ':' + s.pts.length + ':' + sk.bones.join(',') + ':' + sk.falloff;
    const hit = doc._skin.get(s);
    if (hit && hit.key === key) return hit.w;

    const B = boneWorld(doc, {}, v);
    const segs = sk.bones.map(id => { const w = B.get(id); return { id: id, a: w, b: boneTip(w) }; });
    const out = [];
    for (const p of s.pts) {
      const wp = toWorld(s, p);                 // rest world - the frame the weights belong to
      let ds = segs.map(g => ({ id: g.id, d: Math.max(SKIN_EPS, segDist(wp, g.a, g.b)) }));
      ds.sort((x, y) => x.d - y.d);
      /* Inside the falloff, nearest SKIN_MAXB by inverse square. A point outside
         every bone's falloff still gets the single nearest one: a shape that is
         bound must stay bound, or part of it would be left behind when the rest
         of it moved. */
      let use = ds.filter(x => !sk.falloff || x.d <= sk.falloff).slice(0, SKIN_MAXB);
      if (!use.length) use = [ds[0]];
      let tot = 0; const ws = use.map(x => { const val = 1 / (x.d * x.d); tot += val; return { b: x.id, w: val }; });
      for (const x of ws) x.w /= tot;
      out.push(ws);
    }
    doc._skin.set(s, { key: key, w: out });
    return out;
  }

  /* THE one hook. Teach this and shapeAt, drawShape, the selection chrome,
     groupBox, finishMarquee, flipSelected, the export crop and the thumbnails
     are all correct for nothing.

     NOTE the explicit frame parameter: call sites used to read
     `grp.flatMap(worldPts)`, which hands this the ARRAY INDEX as a frame. The
     same trap now has a second edge - passing DT.worldPts itself to map would
     hand it a SHAPE as the doc. Always call it, never reference it. */
  function worldPts(doc, s, f, v) {
    const raw = s.pts.map(p => toWorld(s, p));
    const sk = skinOf(doc, s);
    if (!sk || !doc.rig.length) return raw;
    const M = skinMats(doc, f == null ? doc.frame : f, v);
    let moved = false;
    for (const id of sk.bones) { const D = M.get(id); if (D && !D.id) { moved = true; break; } }
    if (!moved) return raw;                     // at rest, and this is the common case
    const W = skinWeights(doc, s, v);
    return raw.map((p, i) => {
      const ws = W[i];
      let x = 0, y = 0, tot = 0;
      for (const e of ws) {
        const D = M.get(e.b); if (!D) continue;
        const q = applyD(D, p); x += q.x * e.w; y += q.y * e.w; tot += e.w;
      }
      return tot > 0 ? { x: x / tot, y: y / tot } : p;
    });
  }

  /* Whether a shape is currently displaced from where it was drawn. Point
     editing writes back through toLocal, which knows nothing about any of this,
     so Smear, Eraser and the outline warp are off while it is true. */
  function deformed(doc, s, f, v) {
    const sk = skinOf(doc, s);
    if (!sk) return false;
    const M = skinMats(doc, f == null ? doc.frame : f, v);
    for (const id of sk.bones) { const D = M.get(id); if (D && !D.id) return true; }
    return false;
  }

  /* A reference's pts are its placement box, not an outline, so it cannot be
     point-deformed - it binds to exactly ONE bone and moves rigidly. With a
     single weight of 1 the blend above and this composition are the same map,
     so worldPts still gives the right box:
        D . T(x,y) . R(rot) . S(sx,sy)
          = T(D(x,y)) . R(rot+dtheta) . S(k.sx, k.sy)
     because a uniform k commutes with R and with the diagonal S. That is the
     same argument placeRef relies on, and it is why a negative sx from a flip
     survives: nothing here ever decomposes the shape's own matrix. */
  function posedPlacement(doc, s, f, v) {
    const sk = skinOf(doc, s);
    if (!sk) return s;
    const M = skinMats(doc, f == null ? doc.frame : f, v);
    const D = M.get(sk.bones[0]);
    if (!D || D.id) return s;
    const o = applyD(D, { x: s.x, y: s.y });
    return { x: o.x, y: o.y, rot: s.rot + Math.atan2(D.n, D.c), sx: s.sx * D.k, sy: s.sy * D.k };
  }

  /* ============================================================== painting
     Every painter takes its 2d context `g` as its FIRST argument. In the editor
     these all reached for a module-level `const ctx`, which is exactly what
     made a second canvas impossible - and note the export path never needed a
     second one, it retargets the single canvas with setTransform. The game
     passes its own context and brackets each actor in save/setTransform/restore,
     which is why no camera plumbing appears anywhere in this file. */

  const paint = c => c === NONE ? 'rgba(0,0,0,0)' : c;   // for gradient stops

  const HATCH_GAP = 5.5;     // fixed, so the texture reads the same on every shape
  const HATCH_WEIGHT = 0.5;  // share of the gap each line fills
  const REF_MAX_DEPTH = 4;

  function fillStyleFor(g, doc, b, s) {
    const t = terminatorArc(b, doc.lightFrom, doc.lightTo);
    const gr = g.createRadialGradient(t.L.x, t.L.y, 0, t.L.x, t.L.y, t.R / TERMINATOR);
    gr.addColorStop(0, paint(s.colors.fill));
    gr.addColorStop(Math.max(0, TERMINATOR - SOFTNESS), paint(s.colors.fill));
    gr.addColorStop(Math.min(1, TERMINATOR + SOFTNESS), paint(s.colors.shadow));
    gr.addColorStop(1, paint(s.colors.shadow));
    return gr;
  }

  /* Engraver's shading: flat fill, then ONE band of 45-degree hatch lines at a
     single weight - the same one tone the gradient mode gives, just drawn as
     line texture. The band is clipped to the far side of the same terminator
     arc the gradient uses, so both modes break on exactly the same curve. */
  function hatchShade(g, doc, b, s) {
    const diag = Math.hypot(b.w, b.h) || 1;
    if (diag < 36) return;                            // too small to read as texture
    const hd = { x: Math.SQRT1_2, y: Math.SQRT1_2 };  // hatch lines, fixed 45 degrees
    const hs = { x: Math.SQRT1_2, y: -Math.SQRT1_2 }; // and the direction we step them

    // only step across the span the box actually occupies
    let k0 = 1e9, k1 = -1e9;
    [[b.x0, b.y0], [b.x1, b.y0], [b.x1, b.y1], [b.x0, b.y1]].forEach(function (p) {
      const k = (p[0] - b.cx) * hs.x + (p[1] - b.cy) * hs.y;
      if (k < k0) k0 = k; if (k > k1) k1 = k;
    });

    const t = terminatorArc(b, doc.lightFrom, doc.lightTo);
    g.save();
    g.beginPath();                                    // everything beyond the arc
    g.rect(b.x0 - diag, b.y0 - diag, b.w + diag * 2, b.h + diag * 2);
    g.moveTo(t.L.x + t.R, t.L.y);
    g.arc(t.L.x, t.L.y, t.R, 0, TAU);
    g.clip('evenodd');

    g.strokeStyle = s.colors.shadow; g.lineCap = 'butt';
    g.lineWidth = HATCH_GAP * HATCH_WEIGHT;
    for (let k = k0 - HATCH_GAP; k <= k1 + HATCH_GAP; k += HATCH_GAP) {
      const cx = b.cx + hs.x * k, cy = b.cy + hs.y * k;
      g.beginPath();
      g.moveTo(cx - hd.x * diag, cy - hd.y * diag);
      g.lineTo(cx + hd.x * diag, cy + hd.y * diag);
      g.stroke();
    }
    g.restore();
  }

  /* Which frame of a reference to draw. Pinned by default - an eye sheet is a
     set of expressions a game swaps between, not something that plays on its
     own - but an instance can be set to FOLLOW, and then it walks in step with
     whatever frame the parent is showing, wrapping when it is the shorter. */
  function refFrames(lib) { return (lib.views || {})[Object.keys(lib.views || {})[0]] || []; }
  function refFrameIndex(rf, lib, pframe) {
    const frames = refFrames(lib), n = frames.length || 1;
    if (rf.follow) return ((pframe || 0) % n + n) % n;
    return Math.max(0, Math.min(n - 1, rf.frame || 0));
  }

  /* An imported drawing. Draw its frame through the reference's own transform,
     which makes it a STAMP rather than a re-lit shape: the sub-shapes' light
     axis and hatch gap are evaluated in the reference's local frame, so
     rotating one rotates its light with it and scaling one scales its hatch.
     For a rigid imported asset that is the more predictable of the two - it
     looks exactly as it was authored.

     An item may import another item, so a sub-shape can itself be a reference
     and this recurses through drawShape. depth is the only thing stopping it:
     a cycle is reachable once two items reference each other. */
  function drawRefShape(g, doc, s, opts) {
    const o = opts || {};
    const depth = o.depth || 0;
    if (depth >= REF_MAX_DEPTH) return;
    const lib = doc.refLib.get(s.ref.key);
    if (!lib) return;
    // REST_F is not a frame of anything - "follow" still means the frame you are on
    const ff = (o.pframe == null || o.pframe < 0) ? doc.frame : o.pframe;
    const fi = refFrameIndex(s.ref, lib, ff);
    const fr = refFrames(lib)[fi];
    if (!fr || !fr.length) return;
    g.save();
    // A reference binds to one bone and moves rigidly - see posedPlacement.
    const pl = posedPlacement(doc, s, o.pframe, o.pview);
    g.translate(pl.x, pl.y); g.rotate(pl.rot); g.scale(pl.sx, pl.sy);
    /* opts is forwarded near-verbatim: drawShape ASSIGNS globalAlpha rather
       than multiplying it, so an alpha set out here would be thrown away and
       the onion skin would draw an imported drawing at full strength. Only
       depth and the parent frame change on the way down - a nested reference
       follows the frame of the reference holding it, not the document's. */
    const sub = { ghost: o.ghost, depth: depth + 1, pframe: fi };
    for (const x of fr) drawShape(g, doc, x, sub);
    g.restore();
  }

  function drawShape(g, doc, s, opts) {
    if (s.ref) { drawRefShape(g, doc, s, opts); return; }
    const ghost = opts && opts.ghost;
    /* The frame is passed through so the onion of frame n-1 is deformed by
       frame n-1's pose, and the other view by the current one. Without it both
       would be posed by whichever frame happens to be showing - and the VIEW
       with it, since each view now has a rest skeleton of its own. */
    const wp = worldPts(doc, s, opts && opts.pframe, opts && opts.pview);
    if (wp.length < 3) return;
    const b = bbox(wp);
    const closed = s.closed !== false;
    const hatching = doc.shading === 'hatch' && !ghost;

    g.save();
    if (ghost) g.globalAlpha = 0.13;

    buildFill(g, wp, closed);                   // the fill closes whether the outline does or not

    /* One layer of shading and no more. There used to be a soft contact shadow
       cast outside each shape, which landed on whatever sat underneath and gave
       those shapes a second, darker band on top of their own shading.
       NONE in a slot switches that part off. Fill and shadow are independent:
       no fill leaves the silhouette see-through, no shadow leaves it flat. */
    const noFill = s.colors.fill === NONE, noShadow = s.colors.shadow === NONE;
    if (hatching || noShadow) {
      if (!noFill) { g.fillStyle = s.colors.fill; g.fill(); }
    } else {
      g.fillStyle = fillStyleFor(g, doc, b, s); g.fill();
    }

    if (hatching && !noShadow) {                // hatch inside the silhouette
      g.save(); g.clip(); hatchShade(g, doc, b, s); g.restore();
    }

    // hatchShade tramples the current path, so rebuild before stroking
    if (s.colors.outline !== NONE) {
      if (closed) buildPath(g, wp); else buildOpenPath(g, wp);
      g.lineJoin = 'round';
      g.lineCap = closed ? 'round' : 'butt';    // butt: the outline stops flush with the chord
      g.strokeStyle = s.colors.outline; g.lineWidth = s.lw;
      g.stroke();
    }
    g.restore();
  }

  /* The whole of what a game's render loop needs on top of drawShape: draw a
     frame's worth of shapes in array order (later = on top). */
  function drawFrameShapes(g, doc, shapes, opts) {
    for (const s of shapes) drawShape(g, doc, s, opts);
  }

  /* ========================================================= the scene format
     `migrateScene` is the seam every later version steps through, and it is the
     ONE piece the editor and the game must never have two copies of: a format
     change has to land in a single place, and a scene newer than the runtime
     has to throw for both readers rather than half-load. The editor's
     sceneFromJSON and the game's docFromScene are two different READERS over
     the same migrated object - that is a deliberate cost, and sharing this
     function plus SCENE_VERSION is what stops them drifting. */

  const SCENE_FORMAT = 'charactersmith.scene';
  const SCENE_VERSION = 6;   // v6 made a document hold MANY named animations
  const FPS = 12;

  const DOC_KINDS = {
    character: { label: 'Image', views: [['front', 'Front'], ['back', 'Back']], frames: 'free', ref: false },
    item: { label: 'Item', views: [['front', 'Front'], ['back', 'Back']], frames: 'free', ref: true },
    eyes: {
      label: 'Eyes', views: [['main', 'Main']], frames: 'fixed', ref: true,
      frameNames: ['Normal', 'Blink', 'Suspicious', 'Surprised', 'Angry', 'Sad']
    },
    mouths: {
      label: 'Mouths', views: [['main', 'Main']], frames: 'fixed', ref: true,
      frameNames: ['Closed', 'Open', 'Happy', 'Sad', 'Screaming']
    }
  };

  const STD_ANIMS = ['Idle', 'Walk', 'Run', 'Jump', 'Land', 'Hurt', 'Fall', 'Die', 'Throw', 'Attack Melee'];

  /* A v2 refs entry was {frameOrder:[name], frames:{name:[shape]}} - one sheet,
     one expression per key. In v3 it is shaped like a document: one view
     holding an array of frames, in the sheet's own order. */
  function migrateRefEntry(e) {
    if (!e || e.views) return e;                 // already v3
    const order = (e.frameOrder || []).slice();
    return {
      kind: e.kind, title: e.title, drawingId: e.drawingId, rev: e.rev,
      tags: e.tags || [], author: e.author || '',
      frameNames: order, frameCount: Math.max(1, order.length),
      views: { main: order.map(n => (e.frames || {})[n] || []) },
      refs: {}
    };
  }
  function migrateRefField(rf, entry) {
    if (rf.frame != null) return;                // already v3
    const order = (entry && entry.frameNames) || [];
    const i = order.indexOf(rf.pose);
    rf.frame = i >= 0 ? i : 0;
    rf.follow = false;
    delete rf.pose;
  }

  function migrateScene(o) {
    if (!o || o.format !== SCENE_FORMAT) throw new Error('Not a Drawthing scene.');
    if (o.version > SCENE_VERSION)
      throw new Error('This scene is version ' + o.version + ', the editor only reads up to ' + SCENE_VERSION + '.');
    if (o.version < 2) {                          // v1 knew only the two character views
      o.kind = 'character';
      o.viewOrder = ['front', 'back'];
      o.refs = {};
      o.version = 2;
    }
    if (o.version < 3) {
      /* v2's views held shape lists. v3's hold frames. For a character that is a
         wrap - one frame, the drawing as it was. For an eye or a mouth sheet the
         expression VIEWS were the frames all along, so they fold into one view in
         the order the sheet declared them, and their old view labels become the
         frame names. */
      const order = (o.viewOrder || []).slice();
      const src = o.views || {};
      if (o.kind === 'eyes' || o.kind === 'mouths') {
        o.frameNames = (DOC_KINDS[o.kind].frameNames || order).slice();
        o.views = { main: order.map(n => src[n] || []) };
        o.viewOrder = ['main'];
        o.frameOrderV2 = order;                   // so a v2 ref.pose can still be resolved
      } else {
        o.frameNames = null;
        o.views = {};
        for (const n of order) o.views[n] = [src[n] || []];
      }
      o.frameCount = Math.max(1, (o.views[o.viewOrder[0]] || []).length);
      const rf = o.refs || {};
      for (const k of Object.keys(rf)) rf[k] = migrateRefEntry(rf[k]);
      // and every shape's ref.pose (a name) becomes ref.frame (an index)
      for (const n of o.viewOrder) for (const fr of o.views[n] || []) for (const s of fr || [])
        if (s && s.ref) migrateRefField(s.ref, rf[s.ref.key]);
      (o.render || (o.render = {})).fps = FPS;
      o.version = 3;
    }
    if (o.version < 4) {
      // Nothing to fold: a v3 drawing simply has no skeleton. AFTER the v3 block,
      // which is what settles frameCount.
      o.bones = { rig: [], bind: {}, pose: [] };
      o.version = 4;
    }
    if (o.version < 5) {
      /* The rest went PER VIEW and the pose became a delta from it. Every view
         starts on the same rest with mirror sense +1, and every delta is measured
         off the old single bind - so a v4 drawing comes out bit-identical, which
         is the point. att/off move off the bone and into the rest, since a
         mirrored view has to be able to hang a child on the other side. */
      const bn = o.bones || { rig: [], bind: {}, pose: [] };
      const rg = bn.rig || [], bind = bn.bind || {};
      const order = o.viewOrder || ['front', 'back'];
      const rest = {};
      for (const v of order) {
        const m = {};
        for (const b of rg) {
          const s0 = bind[b.id] || { len: 0, rot: 0 };
          const e = {
            len: s0.len || 0, rot: s0.rot || 0,
            att: (b.att == null ? 1 : b.att), off: b.off || 0, mx: 1, my: 1
          };
          if (s0.x != null) { e.x = s0.x; e.y = s0.y; }
          m[b.id] = e;
        }
        rest[v] = m;
      }
      for (const b of rg) { delete b.att; delete b.off; }
      const pose = (bn.pose || []).map(pp => {
        const q = {};
        for (const k of Object.keys(pp || {})) {
          const s0 = bind[k] || { len: 0, rot: 0 }, e = pp[k] || {};
          const d = {
            drot: (e.rot || 0) - (s0.rot || 0),
            klen: (s0.len > 0.0001) ? (e.len || 0) / s0.len : 1
          };
          if (s0.x != null || e.x != null) { d.dx = (e.x || 0) - (s0.x || 0); d.dy = (e.y || 0) - (s0.y || 0); }
          // one world goal served both views when both had the same skeleton
          if (e.ikx != null) { d.ik = {}; for (const v of order) d.ik[v] = { x: e.ikx, y: e.iky }; }
          q[k] = d;
        }
        return q;
      });
      o.bones = { rig: rg, rest: rest, pose: pose };
      o.version = 5;
    }
    if (o.version < 6) {
      /* One animation became many. Everything a v5 scene held IS the first one -
         named Idle, because that is the resting state a drawing is made in before
         it is animated - and the standard set is appended behind it, empty. A
         fixed-frame kind is left with its single animation: its frames are the
         expressions a game swaps between, not a timeline. */
      const order = o.viewOrder || Object.keys(o.views || {});
      const vs = o.views || {};
      const nf = Math.max(1, o.frameCount || (vs[order[0]] || []).length || 1);
      const free = (DOC_KINDS[o.kind] || DOC_KINDS.character).frames === 'free';
      const blank = () => {
        const v = {}; for (const k of order) v[k] = [[]];
        return { views: v, pose: [{}], frameCount: 1 };
      };
      o.animations = [{
        name: free ? STD_ANIMS[0] : 'Main', loop: true, pingpong: false,
        frameCount: nf, views: vs, pose: ((o.bones || {}).pose) || []
      }];
      if (free) for (const n of STD_ANIMS.slice(1))
        o.animations.push(Object.assign({ name: n, loop: true, pingpong: false }, blank()));
      o.activeAnim = 0;
      delete o.views; delete o.frameCount;
      if (o.bones) delete o.bones.pose;
      o.version = 6;
    }
    return o;
  }

  /* ======================================================= the game's reader
     docFromScene is NOT sceneFromJSON. The editor's loader writes ~20 globals
     and calls a dozen UI syncs - it is the editor's boot sequence, not a
     parser. This builds a plain Doc and touches nothing else. The two readers
     are a real cost; what stops them drifting is that both go through the
     SHARED migrateScene above, so a format change lands in one place. */

  const viewsOf = kind => (DOC_KINDS[kind] || DOC_KINDS.character).views.map(v => v[0]);
  const framesFree = kind => (DOC_KINDS[kind] || DOC_KINDS.character).frames === 'free';
  const frameCountOf = doc => ((doc.views[doc.viewNames[0]] || []).length) || 1;
  /* The current frame of the current view - the cur() every read must go
     through, because views[view][frame] reaching undefined kills a render. */
  const curFrame = doc => (doc.views[doc.view] || [])[doc.frame] || [];

  function docFromScene(raw, opts) {
    const o = migrateScene(JSON.parse(JSON.stringify(raw)));
    const kind = DOC_KINDS[o.kind] ? o.kind : 'character';
    const viewNames = (o.viewOrder && o.viewOrder.length) ? o.viewOrder.slice() : viewsOf(kind);

    /* Names are unique case-insensitively: a game asks for an animation BY
       NAME, so a duplicate would make one of them unreachable. */
    const seen = new Set();
    const anims = (o.animations || []).map((a, i) => {
      let name = (a.name || ('Anim ' + (i + 1))).trim() || ('Anim ' + (i + 1));
      let k = name.toLowerCase(), n = 2;
      while (seen.has(k)) { name = (a.name || 'Anim') + ' ' + (n++); k = name.toLowerCase(); }
      seen.add(k);
      const views = {};
      let nf = 1;
      for (const v of viewNames) nf = Math.max(nf, ((a.views || {})[v] || []).length);
      nf = Math.max(1, a.frameCount || nf);
      /* EVERY view must carry the same number of frames, in every animation -
         a short one is what makes views[view][frame] undefined mid-render. */
      for (const v of viewNames) {
        const src = ((a.views || {})[v] || []).slice();
        while (src.length < nf) src.push([]);
        src.length = nf;
        views[v] = src;
      }
      const pose = [];
      for (let f = 0; f < nf; f++) pose.push((a.pose || [])[f] || {});
      return {
        name: name, loop: a.loop !== false, pingpong: !!a.pingpong,
        frameCount: nf, views: views, pose: pose
      };
    });
    if (!anims.length) {
      const v = {}; for (const n of viewNames) v[n] = [[]];
      anims.push({ name: framesFree(kind) ? STD_ANIMS[0] : 'Main', loop: true, pingpong: false, frameCount: 1, views: v, pose: [{}] });
    }

    const bones = o.bones || {};
    const rig = (bones.rig || []).map(b => Object.assign({}, b));
    const rigIds = new Set(rig.map(b => b.id));
    /* A view the scene carries no rest for gets a deep COPY of the first
       view's, NEVER a shared reference: two views aliasing one rest would have
       an edit to either silently rewrite the other. */
    const restPose = {};
    const srcRest = bones.rest || {};
    const first = srcRest[viewNames[0]] || srcRest[Object.keys(srcRest)[0]] || {};
    for (const v of viewNames) restPose[v] = JSON.parse(JSON.stringify(srcRest[v] || first));

    const refLib = new Map();
    for (const k of Object.keys(o.refs || {})) refLib.set(k, o.refs[k]);

    const ai = Math.max(0, Math.min(anims.length - 1, o.activeAnim || 0));
    const r = o.render || {}, light = r.light || {};

    const doc = newDoc({
      id: (opts && opts.id) || null,
      title: (opts && opts.title) != null ? opts.title : (o.title || null),
      rev: (opts && opts.rev) || 0,
      kind: kind,
      viewNames: viewNames,
      frameNames: o.frameNames || (DOC_KINDS[kind] || {}).frameNames || null,
      anims: anims, animIdx: ai,
      views: anims[ai].views, bonePose: anims[ai].pose,
      view: viewNames[0], frame: 0,
      rig: rig, restPose: restPose, refLib: refLib,
      shading: r.shading === 'gradient' ? 'gradient' : 'hatch',
      lightFrom: light.from || LIGHT_FROM,
      lightTo: light.to || LIGHT_TO,
      fps: r.fps || FPS,
      canvas: o.canvas || null
    });

    /* A bone id the rig does not hold reads as unbound everywhere, so prune it
       here rather than letting every later skinOf filter it again. */
    for (const a of doc.anims)
      for (const v of viewNames)
        for (const fr of a.views[v])
          for (const s of fr)
            if (s && s.skin && s.skin.bones) {
              s.skin.bones = s.skin.bones.filter(id => rigIds.has(id));
              if (!s.skin.bones.length) delete s.skin;
            }
    return doc;
  }

  /* Switch which animation a Doc is standing in. `views` and `bonePose` ARE the
     current animation's - the same trick the editor uses - so this is a swap of
     exactly those two, plus a rigRev bump because the pose changed. It must
     stay synchronous: a caller's render loop is in flight, and one frame
     landing on a short views[view] or a pose that does not reach `frame`
     throws. */
  function setAnim(doc, i) {
    if (!doc.anims.length) return doc;
    const n = Math.max(0, Math.min(doc.anims.length - 1, i | 0));
    const a = doc.anims[n];
    doc.animIdx = n; doc.views = a.views; doc.bonePose = a.pose;
    doc.frame = Math.min(doc.frame, a.frameCount - 1);
    doc.rigRev++;
    return doc;
  }
  const animIndexByName = (doc, name) => {
    const k = String(name || '').toLowerCase();
    for (let i = 0; i < doc.anims.length; i++) if (doc.anims[i].name.toLowerCase() === k) return i;
    return -1;
  };
  function setAnimByName(doc, name) {
    const i = animIndexByName(doc, name);
    return i < 0 ? doc : setAnim(doc, i);
  }

  /* One actor. Fifty goblins are fifty of these over ONE base Doc: the shapes,
     rig, rest, refLib and the weight cache are shared through the prototype
     (nothing in the read path mutates a shape, and skinWeights' WeakMap.set on
     an inherited map writes to the base's, so the weights are computed once),
     while frame, view, pose and the MATRIX cache are the instance's own -
     which is exactly the split that makes a crowd walking out of phase cheap. */
  function instanceOf(base) {
    const d = Object.create(base);
    d.view = base.viewNames[0]; d.frame = 0;
    d.animIdx = base.animIdx;
    d.views = base.views; d.bonePose = base.bonePose;
    d.rigRev = base.rigRev;
    d._mats = new Map(); d._matQ = [];
    return d;
  }

  /* ---------------------------------------------------------------- export */
  Object.assign(DT, {
    TAU, NONE, PAPER_RGB, TERMINATOR, SOFTNESS, LIGHT_DIST, LIGHT_FROM, LIGHT_TO,
    dist, mid, toWorld, toLocal, bbox, pathLength, segDist, segCross, boxPts,
    buildPath, buildFill, buildOpenPath,
    rdp, rdpLoop, resample, arcLengths, laplacian,
    hex2rgb, clamp255, shade, hexRGB, lowContrast,
    lightAxis, terminatorArc,
    newDoc, bindDoc, bumpRig, bumpBind,
    REST0, SKIN_EPS, SKIN_MAXB, MIN_BONE_K,
    restAt, restBone, poseAt, mirOf, sgnX, sgnY, boneById,
    boneWorld, boneTip, boneAt,
    skinOf, skinMats, skinWeights, applyD,
    worldPts, deformed, posedPlacement,
    HATCH_GAP, HATCH_WEIGHT, REF_MAX_DEPTH, paint,
    fillStyleFor, hatchShade, refFrames, refFrameIndex,
    drawShape, drawRefShape, drawFrameShapes,
    SCENE_FORMAT, SCENE_VERSION, FPS, DOC_KINDS, STD_ANIMS,
    migrateScene, migrateRefEntry, migrateRefField,
    docFromScene, instanceOf, setAnim, setAnimByName, animIndexByName,
    viewsOf, framesFree, frameCountOf, curFrame
  });

  root.DT = DT;
})(typeof window !== 'undefined' ? window : globalThis);
