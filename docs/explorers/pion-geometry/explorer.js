/* The pion geometry explorer: Tr(phi^3) and the pion cone side by side, for six-point scattering.
   A classic script with no requests, so the page also works opened from disk. The exact facts it states
   (which loci are zeros) come from the JSON block in index.html, computed by the builder in rational
   arithmetic; the drawings and the values along the delta-line are computed here in floating point. */
(function () {
  'use strict';
  const DATA = JSON.parse(document.getElementById('explorer-data').textContent);
  const $ = id => document.getElementById(id);

  /* ---------- vectors ---------- */
  const sub3 = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
  const add3 = (a, b, s = 1) => [a[0] + s * b[0], a[1] + s * b[1], a[2] + s * b[2]];
  const dot3 = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const cross3 = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const nrm3 = a => { const l = Math.hypot(...a) || 1; return a.map(x => x / l); };
  const solve3 = (M, r) => {
    const d = dot3(M[0], cross3(M[1], M[2]));
    if (Math.abs(d) < 1e-10) return null;
    const c0 = cross3(M[1], M[2]), c1 = cross3(M[2], M[0]), c2 = cross3(M[0], M[1]);
    return [0, 1, 2].map(i => (r[0] * c0[i] + r[1] * c1[i] + r[2] * c2[i]) / d);
  };

  /* ---------- six-point kinematics ---------- */
  const N = 6, ODD = ['14', '25', '36'], SLIDERS = DATA.sliders;
  const CHORDS = ['13', '14', '15', '24', '25', '26', '35', '36', '46'];
  const norm = (i, j) => { i = ((i - 1) % N + N) % N + 1; j = ((j - 1) % N + N) % N + 1; return i < j ? [i, j] : [j, i]; };
  const adj = (i, j) => { const [a, b] = norm(i, j); return a === b || b - a === 1 || (a === 1 && b === N); };
  /* each linear form on the chart (X13, X35, X15) as [gx, gy, gz, h]: value = g.p + h */
  function chart(c) {
    const f = {
      X13: [1, 0, 0, 0], X35: [0, 1, 0, 0], X15: [0, 0, 1, 0],
      X14: [1, -1, 0, c[35] + c[36]], X24: [0, -1, 0, c[13] + c[35] + c[36]], X25: [-1, 0, 1, c[13] + c[14]],
      X26: [-1, 0, 0, c[13] + c[14] + c[15]], X36: [0, 1, -1, c[15] + c[25]], X46: [0, 0, -1, c[15] + c[25] + c[35]]
    };
    const lin = (a, b, s) => a.map((x, i) => x + s * b[i]);
    f.c24 = lin(lin(f.X24, f.X35, 1), f.X25, -1);
    f.c26 = lin(lin(f.X26, f.X13, 1), f.X36, -1);
    f.c46 = lin(lin(f.X46, f.X15, 1), f.X14, -1);
    return f;
  }
  const val = (f, k, p) => dot3(f[k].slice(0, 3), p) + f[k][3];
  const crosses = (p, q) => { const [a, b, c, d] = [+p[0], +p[1], +q[0], +q[1]]; return (a < c && c < b && b < d) || (c < a && a < d && d < b); };
  const TRI = [];
  for (let i = 0; i < 9; i++) for (let j = i + 1; j < 9; j++) for (let k = j + 1; k < 9; k++) {
    const t = [CHORDS[i], CHORDS[j], CHORDS[k]];
    if (!crosses(t[0], t[1]) && !crosses(t[0], t[2]) && !crosses(t[1], t[2])) TRI.push(t);
  }
  function planarAt(f, p) { const X = {}; CHORDS.forEach(k => { X[k] = val(f, 'X' + k, p); }); return X; }
  function terms(X) {
    const phi = TRI.map(t => 1 / (X[t[0]] * X[t[1]] * X[t[2]]));
    const xv = (i, j) => { const [a, b] = norm(i, j); return adj(a, b) ? 0 : X['' + a + b]; };
    const pi = [];
    for (const s of [0, 2, 4]) {
      const g = (i, j) => xv(i + s, j + s);
      pi.push((g(1, 3) + g(2, 4)) * (g(1, 5) + g(4, 6)) / g(1, 4), -g(1, 3), -g(2, 4));
    }
    return { phi, pi };
  }
  const sum = a => a.reduce((s, x) => s + x, 0);
  function amps(f, p) { const t = terms(planarAt(f, p)); return { phi: sum(t.phi), pion: sum(t.pi) }; }

  /* ---------- the delta-direction and the plane across it ---------- */
  const D = nrm3([1, 1, 1]), E1 = nrm3(cross3(D, [0, 0, 1])), E2 = cross3(D, E1);
  const pl3 = (s, t) => add3(E1.map(x => x * s), E2, t);

  /* ---------- polytopes ---------- */
  function polyH(H) {
    const V = [];
    for (let i = 0; i < H.length; i++) for (let j = i + 1; j < H.length; j++) for (let k = j + 1; k < H.length; k++) {
      const p = solve3([H[i].g, H[j].g, H[k].g], [-H[i].h, -H[j].h, -H[k].h]);
      if (!p) continue;
      if (H.every(q => dot3(q.g, p) + q.h >= -1e-9) && !V.some(v => Math.hypot(...sub3(v, p)) < 1e-7)) V.push(p);
    }
    if (!V.length || V.some(v => v.some(x => Math.abs(x) > 1e3))) return null;
    const ctr = V.reduce((s, v) => add3(s, v), [0, 0, 0]).map(x => x / V.length), F = [];
    if (V.length < 4) return { V, F, ctr }; /* a point, a segment or a triangle: flat, no facets to draw */
    H.forEach(q => {
      const on = V.filter(v => Math.abs(dot3(q.g, v) + q.h) < 1e-7);
      if (on.length < 3) return;
      const out = nrm3(q.g.map(x => -x)), fc = on.reduce((s, v) => add3(s, v), [0, 0, 0]).map(x => x / on.length);
      const e1 = nrm3(sub3(on[0], fc)), e2 = cross3(out, e1);
      const ang = a => Math.atan2(dot3(sub3(a, fc), e2), dot3(sub3(a, fc), e1));
      on.sort((a, b) => ang(a) - ang(b));
      const same = F.find(g => g.pts.length === on.length && g.pts.every(p => on.some(o => Math.hypot(...sub3(o, p)) < 1e-7)));
      if (same) same.lab.push(q.lab); else F.push({ pts: on, out, lab: [q.lab], kind: q.kind });
    });
    return { V, F, ctr };
  }
  function isFlat(V) {
    for (let i = 1; i < V.length; i++) for (let j = i + 1; j < V.length; j++) for (let k = j + 1; k < V.length; k++)
      if (Math.abs(dot3(sub3(V[i], V[0]), cross3(sub3(V[j], V[0]), sub3(V[k], V[0])))) > 1e-6) return false;
    return true;
  }
  function hull2(pts) {
    if (pts.length < 3) return pts.slice();
    pts = pts.slice().sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]), lo = [], hi = [];
    for (const p of pts) { while (lo.length > 1 && cr(lo[lo.length - 2], lo[lo.length - 1], p) <= 1e-12) lo.pop(); lo.push(p); }
    for (const p of pts.slice().reverse()) { while (hi.length > 1 && cr(hi[hi.length - 2], hi[hi.length - 1], p) <= 1e-12) hi.pop(); hi.push(p); }
    return lo.slice(0, -1).concat(hi.slice(0, -1));
  }
  const shadowOf = P => (P ? hull2(P.V.map(v => [dot3(v, E1), dot3(v, E2)])) : []);
  const SLICE_WALLS = ['X14', 'X25', 'X36', 'c24', 'c26', 'c46'];
  function pionSlice(f) {
    let poly = [[-60, -60], [60, -60], [60, 60], [-60, 60]];
    SLICE_WALLS.forEach(k => {
      const v = q => val(f, k, pl3(q[0], q[1])), out = [];
      for (let i = 0; i < poly.length; i++) {
        const a = poly[i], b = poly[(i + 1) % poly.length], va = v(a), vb = v(b);
        if (va >= 0) out.push(a);
        if ((va >= 0) !== (vb >= 0)) { const t = va / (va - vb); out.push([a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])]); }
      }
      /* a wall through a vertex makes the clip emit it twice: keep one */
      const near = (p, q) => Math.hypot(p[0] - q[0], p[1] - q[1]) <= 1e-9;
      poly = [];
      out.forEach(p => { if (!poly.length || !near(p, poly[poly.length - 1])) poly.push(p); });
      while (poly.length > 1 && near(poly[poly.length - 1], poly[0])) poly.pop();
    });
    let A = 0;
    for (let i = 0; i < poly.length; i++) { const p = poly[i], q = poly[(i + 1) % poly.length]; A += p[0] * q[1] - q[0] * p[1]; }
    return { poly, area: Math.abs(A) / 2 };
  }
  const inSlice = (f, q) => SLICE_WALLS.every(k => val(f, k, pl3(q[0], q[1])) > 1e-9);
  const SHIFTED = ['X13', 'X35', 'X15', 'X24', 'X26', 'X46'];
  /* where the delta-line through a slice point is inside the associahedron: p + t D, lo <= t <= hi */
  function lineRange(f, q) {
    const p = pl3(q[0], q[1]);
    let lo = -Infinity, hi = Infinity, lf = '', hf = '';
    SHIFTED.forEach(k => {
      const a = val(f, k, p), b = dot3(f[k].slice(0, 3), D);
      if (Math.abs(b) < 1e-12) { if (a < 0) lo = Infinity; return; }
      const t = -a / b;
      if (b > 0) { if (t > lo) { lo = t; lf = k; } } else if (t < hi) { hi = t; hf = k; }
    });
    /* a line that only grazes the polytope (a point on the shadow's edge) counts as missing it */
    return hi - lo > 1e-9 * Math.max(1, Math.abs(lo), Math.abs(hi)) ? { lo, hi, lf, hf, p } : null;
  }
  function sliceOutsideShadow(sl, sh) {
    if (sh.length < 3) return sl.area > 1e-9;
    const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    return sl.poly.some(q => sh.some((a, i) => cr(a, sh[(i + 1) % sh.length], q) < -1e-7));
  }

  /* ---------- drawing ---------- */
  const S = (t, c) => `<tspan class="it">${t}</tspan><tspan font-size="10" dy="3">${c}</tspan><tspan dy="-3"></tspan>`;
  const esc = s => String(s).replace(/[&<>"]/g, ch => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[ch]);
  function figure(id, fn) {
    const box = $(id), svg = box.querySelector('svg');
    const draw = () => {
      try { const W = box.clientWidth, H = box.clientHeight; if (W > 0) svg.innerHTML = fn(W, H); }
      catch (e) { svg.innerHTML = `<text x="10" y="20">drawing error: ${esc(e.message)}</text>`; }
    };
    new ResizeObserver(draw).observe(box);
    return draw;
  }
  const view = { yaw: -0.7, pitch: 0.35, spin: !matchMedia('(prefers-reduced-motion: reduce)').matches };
  function project(ctr, sc, W, H) {
    const cy = Math.cos(view.yaw), sy = Math.sin(view.yaw), cp = Math.cos(view.pitch), sp = Math.sin(view.pitch);
    const R = p => { const q = sub3(p, ctr), x1 = q[0] * cy + q[2] * sy, z1 = -q[0] * sy + q[2] * cy, y1 = q[1]; return [x1, y1 * cp - z1 * sp, y1 * sp + z1 * cp]; };
    return { R, S: p => { const r = R(p); return [W / 2 + r[0] * sc, H / 2 - r[1] * sc, r[2]]; } };
  }
  const LIGHT = nrm3([-0.45, 0.6, 0.75]);
  const pts2 = (a, pr) => a.map(p => pr.S(p).slice(0, 2).join(',')).join(' ');
  function drawPoly(P, pr, colour) {
    let back = '', front = '', labs = '';
    const o = pr.R(P.ctr);
    P.F.forEach(f => {
      const n = sub3(pr.R(add3(P.ctr, f.out)), o), pts = f.pts.map(pr.S), d = pts.map(p => p.slice(0, 2).join(',')).join(' ');
      if (n[2] <= 0) { back += `<polygon points="${d}" fill="none" stroke="var(--rule)" stroke-dasharray="3 3"/>`; return; }
      const lam = Math.max(0, dot3(nrm3(n), LIGHT)), pct = Math.round(10 + 38 * lam), col = colour(f);
      front += `<polygon points="${d}" style="fill:color-mix(in srgb,${col} ${pct}%,var(--bg))" stroke="${col}" stroke-width="1.3" stroke-linejoin="round"/>`;
      let a = 0;
      for (let i = 0; i < pts.length; i++) { const p = pts[i], q = pts[(i + 1) % pts.length]; a += p[0] * q[1] - q[0] * p[1]; }
      if (Math.abs(a) / 2 > 650) {
        const c = pts.reduce((s, p) => [s[0] + p[0] / pts.length, s[1] + p[1] / pts.length], [0, 0]);
        labs += `<text x="${c[0]}" y="${c[1] + 4}" text-anchor="middle" fill="${col}">${f.lab.map(l => S(l[0], l.slice(1))).join(', ')}</text>`;
      }
    });
    return { back, front, labs };
  }

  /* ---------- state ---------- */
  const EXAMPLES = DATA.examples;
  const st = { c: Object.assign({}, EXAMPLES[0].c), pt: null, note: EXAMPLES[0].note };
  function geometry() {
    const f = chart(st.c);
    const H = ['X13', 'X35', 'X15', 'X14', 'X24', 'X25', 'X26', 'X36', 'X46'].map(k => ({ g: f[k].slice(0, 3), h: f[k][3], lab: k, kind: ODD.includes(k.slice(1)) ? 'odd' : 'even' }));
    const P = polyH(H), sl = pionSlice(f), sh = shadowOf(P);
    const has = sl.poly.length > 2 && sl.area > 1e-9;
    if (has) { if (!st.pt || !inSlice(f, st.pt)) { const n = sl.poly.length; st.pt = [sum(sl.poly.map(q => q[0])) / n, sum(sl.poly.map(q => q[1])) / n]; } }
    else st.pt = null;
    return { f, P, sl, sh, has, flat: P ? isFlat(P.V) : true, ln: st.pt && lineRange(f, st.pt) };
  }

  /* the amplitudes along the delta-line through the chosen point */
  const drawPlot = figure('fig-plot', (W, H) => {
    const g0 = geometry(), { f, ln } = g0;
    if (!st.pt) return `<text x="${W / 2}" y="${H / 2}" text-anchor="middle">No point: the pion slice has no area.</text>`;
    if (!ln) {
      const nl = amps(f, pl3(st.pt[0], st.pt[1])).pion;
      return `<text x="${W / 2}" y="${H / 2 - 22}" text-anchor="middle">This point lies outside the shadow:</text>` +
        `<text x="${W / 2}" y="${H / 2}" text-anchor="middle">its δ-line misses the associahedron.</text>` +
        `<text x="${W / 2}" y="${H / 2 + 22}" text-anchor="middle">The pion amplitude there is ${nl.toPrecision(4)}.</text>`;
    }
    const n = 200, ml = 60, mr = 24, mt = 22, mb = 40, pts = [];
    let nl = 0;
    for (let i = 1; i < n; i++) { const t = ln.lo + (ln.hi - ln.lo) * i / n, a = amps(f, add3(ln.p, D, t)); pts.push([t, a.phi]); nl = a.pion; }
    const pmin = Math.min(...pts.map(p => p[1])), ymax = Math.max(nl * 1.6, pmin * 4, 1e-6);
    if (!Number.isFinite(ymax) || !pts.every(p => Number.isFinite(p[1]))) return `<text x="${W / 2}" y="${H / 2}" text-anchor="middle">The δ-line only grazes the associahedron here.</text>`;
    const X = t => ml + (t - ln.lo) / (ln.hi - ln.lo) * (W - ml - mr), Y = v => H - mb - Math.min(Math.max(v, 0), ymax) / ymax * (H - mt - mb);
    let g = `<line x1="${ml}" y1="${H - mb}" x2="${W - mr}" y2="${H - mb}" stroke="var(--rule)"/><line x1="${ml}" y1="${mt}" x2="${ml}" y2="${H - mb}" stroke="var(--rule)"/>`;
    g += `<text x="${ml - 8}" y="${mt + 4}" text-anchor="end" fill="var(--mute)">${ymax.toPrecision(2)}</text><text x="${ml - 8}" y="${H - mb + 4}" text-anchor="end" fill="var(--mute)">0</text>`;
    g += `<polyline points="${pts.map(p => X(p[0]) + ',' + Y(p[1])).join(' ')}" fill="none" stroke="var(--mute)" stroke-width="2.4"/>`;
    g += `<line x1="${ml}" y1="${Y(nl)}" x2="${W - mr}" y2="${Y(nl)}" stroke="var(--ca)" stroke-width="2.6"/>`;
    g += `<text x="${W - mr}" y="${Y(nl) - 8}" text-anchor="end" fill="var(--ca)">pions: ${nl.toPrecision(4)}, constant</text>`;
    const mid = pts[Math.floor(pts.length / 2)];
    g += `<text x="${X(mid[0])}" y="${Math.max(Y(mid[1]) - 10, mt + 14)}" text-anchor="middle" fill="var(--mute)">Tr(φ³)</text>`;
    g += `<text x="${ml}" y="${H - 12}" fill="var(--mute)">from ${S('X', ln.lf.slice(1))} = 0</text><text x="${W - mr}" y="${H - 12}" text-anchor="end" fill="var(--mute)">to ${S('X', ln.hf.slice(1))} = 0</text>`;
    return g;
  });

  /* the associahedron, its shadow along delta, the pion slice and the delta-line */
  const drawPoly3 = figure('fig-poly', (W, H) => {
    const { f, P, sl, sh, has, flat, ln } = geometry();
    if (!P) return `<text x="${W / 2}" y="${H / 2}" text-anchor="middle">Empty: no point has every planar variable positive.</text>`;
    const along = v => dot3(v, D), ext = Math.max(...P.V.map(v => Math.abs(along(v) - along(P.ctr))));
    const gap = Math.max(0.9, 0.6 * ext), off = along(P.ctr) - ext - gap;
    const onPlane = q => add3(pl3(q[0], q[1]), D, off), drop = v => add3(v, D, off - along(v));
    const top = along(P.ctr) + ext + 0.45 * gap;
    const line = st.pt ? { base: onPlane(st.pt), tip: add3(pl3(st.pt[0], st.pt[1]), D, top) } : null;
    const all = P.V.concat(sh.map(onPlane), line ? [line.base, line.tip] : []);
    const R0 = Math.max(...all.map(v => Math.hypot(...sub3(v, P.ctr)))) || 1;
    const pr = project(P.ctr, Math.min(W, H) / (2.25 * R0), W, H);
    const dr = drawPoly(P, pr, fc => (fc.kind === 'odd' ? 'var(--ca)' : 'var(--mute)'));
    if (!P.F.length) { /* fewer than four vertices: draw the point, segment or triangle itself */
      const s = P.V.map(v => pr.S(v));
      s.forEach((a, i) => s.slice(i + 1).forEach(b => { dr.front += `<line x1="${a[0]}" y1="${a[1]}" x2="${b[0]}" y2="${b[1]}" stroke="var(--mute)" stroke-width="2.5"/>`; }));
      s.forEach(a => { dr.front += `<circle cx="${a[0]}" cy="${a[1]}" r="3.5" fill="var(--mute)"/>`; });
    }
    let plane = sh.length > 2 ? `<polygon points="${pts2(sh.map(onPlane), pr)}" fill="var(--faint)" stroke="var(--mute)"/>` : '';
    if (has) plane += `<polygon points="${pts2(sl.poly.map(onPlane), pr)}" style="fill:color-mix(in srgb,var(--ca) 30%,var(--bg))" stroke="var(--ca)" stroke-width="2"/>`;
    const rays = P.V.map(v => { const a = pr.S(v), b = pr.S(drop(v)); return `<line x1="${a[0]}" y1="${a[1]}" x2="${b[0]}" y2="${b[1]}" stroke="var(--rule)" stroke-width="0.9"/>`; }).join('');
    const planeFront = pr.R(onPlane([0, 0]))[2] > pr.R(P.ctr)[2];
    let g = planeFront ? rays + dr.back + dr.front + dr.labs + plane : plane + rays + dr.back + dr.front + dr.labs;
    if (line) {
      const b = pr.S(line.base), t = pr.S(line.tip);
      g += `<line x1="${b[0]}" y1="${b[1]}" x2="${t[0]}" y2="${t[1]}" stroke="var(--ink)" stroke-width="1.4" stroke-dasharray="4 3" marker-end="url(#arrow)"/>`;
      if (ln) {
        const a = pr.S(add3(ln.p, D, ln.lo)), c = pr.S(add3(ln.p, D, ln.hi));
        g += `<line x1="${a[0]}" y1="${a[1]}" x2="${c[0]}" y2="${c[1]}" stroke="var(--ink)" stroke-width="3.2"/><circle cx="${a[0]}" cy="${a[1]}" r="3.5" fill="var(--ink)"/><circle cx="${c[0]}" cy="${c[1]}" r="3.5" fill="var(--ink)"/>`;
      }
      const ux = t[0] - b[0], uy = t[1] - b[1], ul = Math.hypot(ux, uy) || 1;
      const lx = Math.min(W - 12, Math.max(12, t[0] + ux / ul * 16)), ly = Math.min(H - 6, Math.max(14, t[1] + uy / ul * 16 + 4));
      g += `<circle cx="${b[0]}" cy="${b[1]}" r="6" fill="var(--ink)" stroke="var(--bg)" stroke-width="2"/><text x="${lx}" y="${ly}" text-anchor="middle" font-weight="600">δ</text>`;
    }
    if (flat) g += `<text x="${W / 2}" y="22" text-anchor="middle" fill="var(--ok)" font-weight="600">flat: lower-dimensional, so Tr(φ³) vanishes</text>`;
    return `<defs><marker id="arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="var(--ink)"/></marker></defs>` + g;
  });

  /* looking straight down delta: the shadow and the pion slice */
  let pick = null;
  const drawPlane = figure('fig-plane', (W, H) => {
    const { f, sl, sh, has } = geometry(), all = (has ? sl.poly : []).concat(sh);
    if (!all.length) { pick = null; return `<text x="${W / 2}" y="${H / 2}" text-anchor="middle">No shadow and no slice.</text>`; }
    const xs = all.map(q => q[0]), ys = all.map(q => q[1]), x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys), m = 64;
    const sc = Math.min((W - 2 * m) / (x1 - x0 || 1), (H - 2 * m) / (y1 - y0 || 1)), ox = (W - sc * (x1 - x0)) / 2 - x0 * sc, oy = (H + sc * (y1 - y0)) / 2 + y0 * sc;
    pick = { sc, ox, oy };
    const P2 = q => [ox + q[0] * sc, oy - q[1] * sc];
    let g = sh.length > 2 ? `<polygon points="${sh.map(q => P2(q).join(',')).join(' ')}" fill="var(--faint)"/>` : '';
    if (has) {
      const C = P2([sum(sl.poly.map(q => q[0])) / sl.poly.length, sum(sl.poly.map(q => q[1])) / sl.poly.length]);
      g += `<polygon points="${sl.poly.map(q => P2(q).join(',')).join(' ')}" style="fill:color-mix(in srgb,var(--ca) 22%,var(--bg))"/>`;
      sl.poly.forEach((p, i) => {
        const q = sl.poly[(i + 1) % sl.poly.length], mid = [(p[0] + q[0]) / 2, (p[1] + q[1]) / 2];
        const k = SLICE_WALLS.find(w => Math.abs(val(f, w, pl3(mid[0], mid[1]))) < 1e-7);
        if (!k) return;
        const odd = k[0] === 'X', a = P2(p), b = P2(q), mx = (a[0] + b[0]) / 2, my = (a[1] + b[1]) / 2, dx = mx - C[0], dy = my - C[1], l = Math.hypot(dx, dy) || 1;
        g += `<line x1="${a[0]}" y1="${a[1]}" x2="${b[0]}" y2="${b[1]}" stroke="${odd ? 'var(--ca)' : 'var(--pr)'}" stroke-width="${odd ? 3 : 2.2}" ${odd ? '' : 'stroke-dasharray="6 4"'}/>`;
        g += `<text x="${mx + dx / l * 18}" y="${my + dy / l * 18 + 4}" text-anchor="middle" fill="${odd ? 'var(--ca)' : 'var(--pr)'}">${S(k[0], k.slice(1))}${odd ? ' pole' : ' cancelled'}</text>`;
      });
    } else g += `<text x="${W / 2}" y="26" text-anchor="middle" fill="var(--ok)" font-weight="600">the pion slice collapses: no area</text>`;
    if (sh.length > 2) g += `<polygon points="${sh.map(q => P2(q).join(',')).join(' ')}" fill="none" stroke="var(--mute)" stroke-width="1.4" stroke-dasharray="5 4"/>`;
    if (st.pt) { const p = P2(st.pt); g += `<circle cx="${p[0]}" cy="${p[1]}" r="7" fill="var(--ink)" stroke="var(--bg)" stroke-width="2"/>`; }
    return g;
  });

  /* ---------- zeros: the exact table, and a floating-point check ---------- */
  function numericZeros(f) {
    let zp = true, zn = true, n = 0, seed = 1;
    const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
    for (let t = 0; t < 80 && n < 5; t++) {
      const X = planarAt(f, [rnd() * 8 - 4, rnd() * 8 - 4, rnd() * 8 - 4]);
      if (Object.values(X).some(v => Math.abs(v) < 1e-3)) continue;
      n++;
      const tm = terms(X);
      if (Math.abs(sum(tm.phi)) > 1e-9 * sum(tm.phi.map(Math.abs))) zp = false;
      if (Math.abs(sum(tm.pi)) > 1e-9 * sum(tm.pi.map(Math.abs))) zn = false;
    }
    return { trphi3: zp, pion: zn };
  }
  function zeros(f) {
    const key = SLIDERS.filter(k => +st.c[k] === 0).join(','), exact = DATA.zeros[key], num = numericZeros(f);
    return { key, exact, orders: DATA.orders[key], agree: exact.trphi3 === num.trphi3 && exact.pion === num.pion };
  }

  /* ---------- the outputs below the views ---------- */
  const SHIFT = { 13: '−δ', 35: '−δ', 15: '−δ', 24: '+δ', 26: '+δ', 46: '+δ' };
  function readouts() {
    const g0 = geometry(), { f, P, sl, sh, has, flat, ln } = g0, z = zeros(f), o = z.orders;
    $('fig-poly').classList.toggle('zero', z.exact.trphi3);
    $('fig-plane').classList.toggle('zero', z.exact.pion);
    /* the live regions change only when their text does, so a dragged slider does not flood a screen reader */
    if ($('note').textContent !== st.note) $('note').textContent = st.note;

    const cs = z.key ? z.key.split(',').map(k => `<span class="cz"><var>c</var><sub>${k}</sub></span>`).join(' ') : '<span class="none">no mesh variable at 0</span>';
    const pionLine = !z.key ? 'No mesh variable at 0: generic kinematics.'
      : o.pion > 0 ? `<b class="ok">Pion amplitude: zero of order ${o.pion}.</b> The zeros outweigh the poles.`
        : 'Pion amplitude: finite, no zero. The poles balance the zeros.';
    const phiLine = !z.key ? '' : o.trphi3 > 0 ? `<b class="ok">Tr(φ³): zero of order ${o.trphi3}</b> (it has no prefactor; its associahedron goes flat).` : 'Tr(φ³): no zero here.';
    const balance =
      `<div class="bal"><span>Zeros of ∏ <var>c</var></span><span>${cs}</span><span class="n">${o.dressing}</span></div>` +
      `<div class="bal"><span>Poles of Ω</span><span>${o.omega < 0 ? 'on these walls' : '<span class="none">none here</span>'}</span><span class="n">${-o.omega}</span></div>` +
      `<p>${pionLine}</p>` + (phiLine ? `<p>${phiLine}</p>` : '') +
      (z.agree ? '' : '<p class="warn">The floating-point check disagrees with the exact table here.</p>');
    if ($('balance').innerHTML !== balance) $('balance').innerHTML = balance;

    if (!st.pt) { $('values').innerHTML = '<tr><td>No point: the pion slice has no area at these values.</td></tr>'; }
    else {
      const p3 = ln ? add3(ln.p, D, (ln.lo + ln.hi) / 2) : pl3(st.pt[0], st.pt[1]);
      const X = planarAt(f, p3), a = amps(f, p3);
      const cell = (k, v, note) => `<tr><th>${k}</th><td class="num">${v.toPrecision(4)}</td><td class="small">${note}</td></tr>`;
      const where = ln ? 'at the middle of the δ-line' : 'on the plane (the δ-line misses the associahedron)';
      let rows = ODD.map(k => cell(`<var>X</var><sub>${k}</sub>`, X[k], 'odd: δ leaves it')).join('');
      rows += ['24', '26', '46'].map(k => cell(`<var>c</var><sub>${k}</sub>`, val(f, 'c' + k, p3), 'mesh: δ leaves it')).join('');
      rows += ['13', '35', '15', '24', '26', '46'].map(k => cell(`<var>X</var><sub>${k}</sub>`, X[k], `moves by ${SHIFT[k]}; ${where}`)).join('');
      rows += `<tr><th>Tr(φ³)</th><td class="num">${ln ? a.phi.toPrecision(4) : '–'}</td><td class="small">${ln ? 'at the middle of the δ-line' : 'no point of the line is inside the associahedron'}</td></tr>`;
      rows += `<tr><th>pions</th><td class="num">${a.pion.toPrecision(4)}</td><td class="small">the same all along the δ-line</td></tr>`;
      $('values').innerHTML = rows;
    }
    const outside = has && sliceOutsideShadow(sl, sh);
    $('geom').textContent = `Tr(φ³): ${!P ? 'empty' : flat ? 'flat, lower-dimensional' : `a polytope with ${P.V.length} vertices and ${P.F.length} facets`}. Pions: ${has ? `a slice with ${sl.poly.length} vertices, area ${sl.area.toFixed(3)}${outside ? ', partly outside the shadow' : ''}` : 'the slice collapses, no area'}.`;
  }
  function redraw() { drawPlot(); drawPoly3(); drawPlane(); readouts(); }

  /* ---------- inputs ---------- */
  $('sliders').innerHTML = SLIDERS.map(k => `<div class="slider"><label for="s${k}"><var>c</var><sub>${k}</sub></label><input id="s${k}" type="range" min="0" max="2.5" step="0.05"><output id="o${k}" for="s${k}"></output></div>`).join('');
  function setSliders() { SLIDERS.forEach(k => { $('s' + k).value = st.c[k]; $('o' + k).textContent = (+st.c[k]).toFixed(2); }); }
  SLIDERS.forEach(k => $('s' + k).addEventListener('input', e => {
    st.c[k] = +e.target.value; $('o' + k).textContent = st.c[k].toFixed(2);
    st.note = 'Your own values. The six mesh variables shape the associahedron; for the pions they only choose the slice.';
    document.querySelectorAll('#examples button').forEach(b => b.setAttribute('aria-pressed', 'false'));
    redraw();
  }));
  $('examples').innerHTML = EXAMPLES.map((x, i) => `<button type="button" data-i="${i}" aria-pressed="${i === 0}">${esc(x.name)}</button>`).join('');
  $('examples').addEventListener('click', e => {
    const b = e.target.closest('button');
    if (!b) return;
    const x = EXAMPLES[+b.dataset.i];
    st.c = Object.assign({}, x.c); st.note = x.note; st.pt = null;
    document.querySelectorAll('#examples button').forEach(o => o.setAttribute('aria-pressed', String(o === b)));
    setSliders(); redraw();
  });

  /* rotate the polytope by dragging; pick a point in the plane view */
  {
    const box = $('fig-poly');
    let last = null;
    box.addEventListener('pointerdown', e => { last = [e.clientX, e.clientY]; view.spin = false; box.setPointerCapture(e.pointerId); });
    box.addEventListener('pointermove', e => {
      if (!last) return;
      view.yaw += (e.clientX - last[0]) * 0.01; view.pitch = Math.max(-1.5, Math.min(1.5, view.pitch + (e.clientY - last[1]) * 0.01));
      last = [e.clientX, e.clientY]; drawPoly3();
    });
    const up = () => { last = null; };
    /* keys: the arrows rotate the polytope */
    box.addEventListener('keydown', e => {
      const d = { ArrowLeft: [-0.1, 0], ArrowRight: [0.1, 0], ArrowUp: [0, -0.1], ArrowDown: [0, 0.1] }[e.key];
      if (!d) return;
      e.preventDefault(); view.spin = false;
      view.yaw += d[0]; view.pitch = Math.max(-1.5, Math.min(1.5, view.pitch + d[1])); drawPoly3();
    });
    box.addEventListener('pointerup', up); box.addEventListener('pointercancel', up);
  }
  {
    const box = $('fig-plane');
    let down = false;
    const choose = e => {
      if (!pick) return;
      const r = box.getBoundingClientRect(), q = [(e.clientX - r.left - pick.ox) / pick.sc, (pick.oy - (e.clientY - r.top)) / pick.sc];
      if (inSlice(chart(st.c), q)) { st.pt = q; redraw(); }
    };
    box.addEventListener('pointerdown', e => { down = true; box.setPointerCapture(e.pointerId); choose(e); });
    box.addEventListener('pointermove', e => { if (down) choose(e); });
    box.addEventListener('pointerup', () => { down = false; }); box.addEventListener('pointercancel', () => { down = false; });
    /* keys: the arrows move the point, by a twentieth of the slice's size, while it stays inside */
    box.addEventListener('keydown', e => {
      const d = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, 1], ArrowDown: [0, -1] }[e.key];
      if (!d || !st.pt) return;
      e.preventDefault();
      const sl = pionSlice(chart(st.c)), xs = sl.poly.map(q => q[0]), ys = sl.poly.map(q => q[1]);
      const step = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) / 20;
      const q = [st.pt[0] + d[0] * step, st.pt[1] + d[1] * step];
      if (inSlice(chart(st.c), q)) { st.pt = q; redraw(); }
    });
  }
  /* colour themes: the CSS swaps the colours; the text names whichever the theme shows */
  const THEMES = { default: { pole: 'red', zero: 'green', mesh: 'blue' }, cvd: { pole: 'orange', zero: 'purple', mesh: 'blue' } };
  const words = [...document.querySelectorAll('.cw')];
  words.forEach(s => { s.dataset.cap = /^[A-Z]/.test(s.textContent) ? '1' : ''; });
  const applyTheme = value => {
    const name = THEMES[value] ? value : 'default';
    document.documentElement.dataset.palette = name;
    words.forEach(s => { const w = THEMES[name][s.dataset.role]; s.textContent = s.dataset.cap ? w[0].toUpperCase() + w.slice(1) : w; });
  };
  $('theme').addEventListener('change', e => { applyTheme(e.target.value); redraw(); });
  applyTheme($('theme').value); /* a browser may restore the select's choice on reload */
  $('help-toggle').addEventListener('click', () => {
    const open = document.body.classList.toggle('help-open');
    $('help-toggle').setAttribute('aria-expanded', String(open));
    $('help-toggle').textContent = open ? 'Hide help' : 'Show help';
  });

  /* one motion: a slow turn of the polytope until it is dragged */
  let visible = true;
  new IntersectionObserver(es => { visible = es[0].isIntersecting; }).observe($('fig-poly'));
  const spin = () => { if (view.spin && visible && !document.hidden) { view.yaw += 0.004; drawPoly3(); } requestAnimationFrame(spin); };
  requestAnimationFrame(spin);

  setSliders();
  redraw();
})();
