(function() {
  // Hungarian notation...
  var app, fnAddEventListener, fnRequestAnimationFrame;

  fnRequestAnimationFrame = function(fnCallback) {
    var fnAnimFrame;
    fnAnimFrame = window.requestAnimationFrame || window.webkitRequestAnimationFrame || window.mozRequestAnimationFrame || window.oRequestAnimationFrame || window.msRequestAnimationFrame || function(fnCallback) {
      window.setTimeout(fnCallback, 1000 / 60);
    };
    fnAnimFrame(fnCallback);
  };

  fnAddEventListener = function(o, sEvent, fn) {
    if (o.addEventListener) {
      o.addEventListener(sEvent, fn, false);
    } else {
      o['on' + sEvent] = fn;
    }
  };

  app = function() {
    var Particle, SpatialGrid, ctxRender, fAngle, fCosAngle, fMaxAX, fMaxAY, fMaxAZ, fPI, fSinAngle, fStartVX, fStartVY, fStartVZ, fVX, fnACos, fnCos, fnMax, fnMin, fnNextFrame, fnRender, fnRnd, fnRnd2, fnSetSize, fnSin, fnSwapList, grid, gui, h, iProjSphereX, iProjSphereY, iRadiusSphere, nBody, oBuffer, oDoc, oRadGrad, oRender, oStats, w;
    // SpatialGrid (unchanged structure, but we'll avoid concatenating neighbors)
    SpatialGrid = class {
      constructor(width, height, cellSize) {
        this.width = width;
        this.height = height;
        this.cellSize = cellSize;
        this.grid = [];
        this.numCols = Math.max(1, Math.ceil(width / cellSize));
        this.numRows = Math.max(1, Math.ceil(height / cellSize));
      }
      clear() {
        // faster clearing: keep outer array and reuse rows
        this.grid.length = 0;
      }
      insert(particle) {
        var col, row;
        col = Math.floor(particle.fProjX / this.cellSize);
        row = Math.floor(particle.fProjY / this.cellSize);
        // clamp indices to avoid insane indexes
        if (col < 0) col = 0;
        if (row < 0) row = 0;
        if (col >= this.numCols) col = this.numCols - 1;
        if (row >= this.numRows) row = this.numRows - 1;
        if (!this.grid[row]) {
          this.grid[row] = [];
        }
        if (!this.grid[row][col]) {
          this.grid[row][col] = [];
        }
        this.grid[row][col].push(particle);
      }
      // iterate neighbors by calling a callback to avoid building arrays
      forEachNeighbor(particle, cb) {
        var col = Math.floor(particle.fProjX / this.cellSize);
        var row = Math.floor(particle.fProjY / this.cellSize);
        if (col < 0) col = 0;
        if (row < 0) row = 0;
        for (let r = -1; r <= 1; r++) {
          const rr = row + r;
          if (!this.grid[rr]) continue;
          for (let c = -1; c <= 1; c++) {
            const cc = col + c;
            const cell = this.grid[rr][cc];
            if (!cell) continue;
            // iterate cell
            for (let k = 0; k < cell.length; k++) {
              cb(cell[k]);
            }
          }
        }
      }
    };

    // stats (optional)
    oStats = new Stats();
    oStats.setMode(0);
    oStats.domElement.style.position = 'absolute';
    oStats.domElement.style.left = '0px';
    oStats.domElement.style.top = '0px';
    //document.body.appendChild(oStats.domElement);

    oDoc = document;
    nBody = oDoc.body;

    fPI = Math.PI;
    fnMax = Math.max;
    fnMin = Math.min;
    fnRnd = Math.random;
    fnRnd2 = function() {
      return 2.0 * fnRnd() - 1.0;
    };
    fnCos = Math.cos;
    fnACos = Math.acos;
    fnSin = Math.sin;

    // sphere & particle defaults
    iRadiusSphere = 150;
    iProjSphereX = 0;
    iProjSphereY = 0;

    fMaxAX = 0.1;
    fMaxAY = 0.1;
    fMaxAZ = 0.1;
    fStartVX = 0.001;
    fStartVY = 0.001;
    fStartVZ = 0.001;
    fAngle = 0.0;
    fSinAngle = 0.0;
    fCosAngle = 0.0;

    window.iFramesToRotate = 2000.0;
    window.iPerspective = 250;
    window.iNewParticlePerFrame = 8; // default safe
    window.fGrowDuration = 200.0;
    window.fWaitDuration = 50.0;
    window.fShrinkDuration = 250.0;
    window.aColor = [255, 128, 128];
    fVX = (2.0 * fPI) / window.iFramesToRotate;

    oRadGrad = null;

    // MOUSE / FADE (use time-based interpolation)
    let lastMouseMoveTime = Date.now();
    let fadeProgress = 1.0;
    const mouseStillThresholdMs = 500; // 0.5s
    const fadeDurationMs = 2000; // 2s
    let fadeTarget = 1.0; // target 0 or 1 based on mouse state

    // rendering
    if (typeof nCanvasRender === 'undefined') {
      var _maybe = document.querySelector('canvas');
      if (_maybe) window.nCanvasRender = _maybe;
      else {
        console.error('No canvas found: please ensure nCanvasRender exists.');
        return;
      }
    }
    ctxRender = nCanvasRender.getContext('2d');

    oRender = { pFirst: null };
    oBuffer = { pFirst: null };

    w = h = 0;
    grid = null;

    // CONNECTION system (persistent) - MODIFIED to use Map
    const connections = [];            // 连接数组（用于遍历渲染）
    const connMap = new Map();         // key -> connectionObj （用于快速查找与可塑性处理）
    let _particleIdCounter = 1;

  // tuning params (you can tweak)
  const maxDistance = 140; // px (squared used)
  const maxDistanceSq = maxDistance * maxDistance;
  const baseRandLinks = 2; // per-frame random long links (global)
  const maxConnPerParticle = 2; // degree cap per particle
  const maxTotalConnections = 220; // safety cap
  const cellSize = 120; // grid cell size

  // chain connection parameters
  const minHop = 28;              // Minimum connection distance (px)
  const maxHop = 120;             // Maximum connection distance (px)
  const minHopSq = minHop * minHop;
  const maxHopSq = maxHop * maxHop;
  const maxDegree = 2;            // Maximum connections per particle (chain)
  const maxChainOps = 70;         // Max chain extension attempts per frame
  const maxConnectionsPerFrame = 28; // Max new connections per frame (safety)

  // Spark system parameters
  const sparks = [];              // Array for spark particles
  const maxSparks = 600;          // Max sparks allowed
  const sparkSpawnOnFlash = 6;    // Sparks per flash event

    // helpers
    function makeConnKey(aId, bId) {
      if (aId < bId) return aId + '-' + bId;
      return bId + '-' + aId;
    }

    fnSetSize = function() {
      nCanvasRender.width = w = window.innerWidth;
      nCanvasRender.height = h = window.innerHeight;
      iProjSphereX = w / 2;
      iProjSphereY = h / 2;
      grid = new SpatialGrid(w, h, cellSize);
      return { w: w, h: h };
    };
    fnSetSize();
    fnAddEventListener(window, 'resize', fnSetSize);

    fnAddEventListener(window, 'mousemove', () => {
      lastMouseMoveTime = Date.now();
      fadeTarget = 1.0;
    });

    // swap linked-list nodes (reuse code)
    fnSwapList = function(p, oSrc, oDst) {
      if (p != null) {
        if (oSrc.pFirst === p) {
          oSrc.pFirst = p.pNext;
          if (p.pNext != null) p.pNext.pPrev = null;
        } else {
          p.pPrev.pNext = p.pNext;
          if (p.pNext != null) p.pNext.pPrev = p.pPrev;
        }
      } else {
        p = new Particle();
      }
      p.pNext = oDst.pFirst;
      if (oDst.pFirst != null) oDst.pFirst.pPrev = p;
      oDst.pFirst = p;
      p.pPrev = null;
      return p;
    };

    Particle = (function() {
      class Particle {
        fnInit() {
          this._id = _particleIdCounter++;
          this.fAngle = fnRnd() * fPI * 2;
          this.fForce = fnACos(fnRnd2());
          this.fAlpha = 0;
          this.bIsDead = false;
          this.iFramesAlive = 0;
          this.fX = iRadiusSphere * fnSin(this.fForce) * fnCos(this.fAngle);
          this.fY = iRadiusSphere * fnSin(this.fForce) * fnSin(this.fAngle);
          this.fZ = iRadiusSphere * fnCos(this.fForce);
          this.fVX = fStartVX * this.fX;
          this.fVY = fStartVY * this.fY;
          this.fVZ = fStartVZ * this.fZ;
          this.fGrowDuration = window.fGrowDuration + fnRnd2() * (window.fGrowDuration / 4.0);
          this.fWaitDuration = window.fWaitDuration + fnRnd2() * (window.fWaitDuration / 4.0);
          this.fShrinkDuration = window.fShrinkDuration + fnRnd2() * (window.fShrinkDuration / 4.0);
          this.fAX = 0.0;
          this.fAY = 0.0;
          this.fAZ = 0.0;
          // per-frame
          this._connCount = 0;
          this.highlight = false;
          this.flashTimer = 0; // Initialize flashTimer
        }
        fnUpdate() {
          if (this.iFramesAlive > this.fGrowDuration + this.fWaitDuration) {
            this.fVX += this.fAX + fMaxAX * fnRnd2();
            this.fVY += this.fAY + fMaxAY * fnRnd2();
            this.fVZ += this.fAZ + fMaxAZ * fnRnd2();
            this.fX += this.fVX;
            this.fY += this.fVY;
            this.fZ += this.fVZ;
          }
          this.fRotX = fCosAngle * this.fX + fSinAngle * this.fZ;
          this.fRotZ = -fSinAngle * this.fX + fCosAngle * this.fZ;
          this.fRadiusCurrent = Math.max(0.01, window.iPerspective / (window.iPerspective - this.fRotZ));
          this.fProjX = this.fRotX * this.fRadiusCurrent + iProjSphereX;
          this.fProjY = this.fY * this.fRadiusCurrent + iProjSphereY;
          this.iFramesAlive += 1;
          if (this.iFramesAlive < this.fGrowDuration) {
            this.fAlpha = this.iFramesAlive * 1.0 / this.fGrowDuration;
          } else if (this.iFramesAlive < this.fGrowDuration + this.fWaitDuration) {
            this.fAlpha = 1.0;
          } else if (this.iFramesAlive < this.fGrowDuration + this.fWaitDuration + this.fShrinkDuration) {
            this.fAlpha = (this.fGrowDuration + this.fWaitDuration + this.fShrinkDuration - this.iFramesAlive) * 1.0 / this.fShrinkDuration;
          } else {
            this.bIsDead = true;
          }
          if (this.bIsDead === true) {
            fnSwapList(this, oRender, oBuffer);
          }
          this.fAlpha *= fnMin(1.0, fnMax(0.5, this.fRotZ / iRadiusSphere));
          this.fAlpha = fnMin(1.0, fnMax(0.0, this.fAlpha));
        }
      };

      Particle.prototype.fX = 0.0;
      Particle.prototype.fY = 0.0;
      Particle.prototype.fZ = 0.0;
      Particle.prototype.fVX = 0.0;
      Particle.prototype.fVY = 0.0;
      Particle.prototype.fVZ = 0.0;
      Particle.prototype.fAX = 0.0;
      Particle.prototype.fAY = 0.0;
      Particle.prototype.fAZ = 0.0;
      Particle.prototype.fProjX = 0.0;
      Particle.prototype.fProjY = 0.0;
      Particle.prototype.fRotX = 0.0;
      Particle.prototype.fRotZ = 0.0;
      Particle.prototype.pPrev = null;
      Particle.prototype.pNext = null;
      Particle.prototype.fAngle = 0.0;
      Particle.prototype.fForce = 0.0;
      Particle.prototype.fGrowDuration = 0.0;
      Particle.prototype.fWaitDuration = 0.0;
      Particle.prototype.fShrinkDuration = 0.0;
      Particle.prototype.fRadiusCurrent = 0.0;
      Particle.prototype.iFramesAlive = 0;
      Particle.prototype.bIsDead = false;
      Particle.prototype.highlight = false;
      Particle.prototype._connCount = 0;
      return Particle;
    }).call(this);

    // utility: gather active particles into array (reused to avoid new allocations where possible)
    const tempParticles = [];
    function collectParticles(renderList, outArr) {
      outArr.length = 0;
      for (let p = renderList.pFirst; p != null; p = p.pNext) {
        if (!p.bIsDead) outArr.push(p);
      }
    }

    // Update & prune connections each frame - MODIFIED with weight decay
function pruneConnectionsAndReveal() {
  // iterate backwards to allow safe splice
  for (let k = connections.length - 1; k >= 0; k--) {
    const c = connections[k];
    // decay life and weight over time
    c.life--;
    c.weight *= 0.996; // slow weight decay

    // 当正在 fade-out（fadeProgress 下降）时，加速衰减：让链条与淡出同步
    // (1 - fadeProgress) 越大衰减越快
    if (fadeProgress < 0.9) {
      // 在低于 0.9 时开始轻微加速衰减，倍率平滑
      const extraDecay = Math.ceil((1.0 - fadeProgress) * 2.0); // 0..2
      c.life -= extraDecay;
      c.weight *= (1.0 - (1.0 - fadeProgress) * 0.06); // 轻微额外权重损失
    }

    // remove if life exhausted, refs invalid, or weight too small
    if (c.life <= 0 || !c.aRef || !c.bRef || c.aRef.bIsDead || c.bRef.bIsDead || c.weight < 0.045) {
      if (c.aRef) c.aRef._connCount = Math.max(0, c.aRef._connCount - 1);
      if (c.bRef) c.bRef._connCount = Math.max(0, c.bRef._connCount - 1);
      const key = makeConnKey(c.aId, c.bId);
      connMap.delete(key);
      connections.splice(k, 1);
    }
  }

  // cap total connections (unchanged behaviour)
  if (connections.length > maxTotalConnections) {
    connections.sort((A, B) => (A.life - B.life) + (A.weight - B.weight));
    while (connections.length > maxTotalConnections) {
      const rem = connections.shift();
      if (rem && rem.aRef) rem.aRef._connCount = Math.max(0, rem.aRef._connCount - 1);
      if (rem && rem.bRef) rem.bRef._connCount = Math.max(0, rem.bRef._connCount - 1);
      connMap.delete(makeConnKey(rem.aId, rem.bId));
    }
  }

  // reset per-particle counts & highlight flags
  for (let i = 0; i < tempParticles.length; i++) {
    const p = tempParticles[i];
    p._connCount = 0;
    p.highlight = false;
  }
  // reassign counts from remaining connections
  for (let i = 0; i < connections.length; i++) {
    const c = connections[i];
    if (c.aRef && c.bRef) {
      c.aRef._connCount++;
      c.bRef._connCount++;
      // mark highlight if weight sizable (weight 与 fadeProgress 共同决定视觉)
      if (c.weight > 0.14 && fadeProgress > 0.15) {
        c.aRef.highlight = true;
        c.bRef.highlight = true;
      }
    }
  }
}

    // Create new connections: MODIFIED with synaptic plasticity
function createConnections() {
  const total = tempParticles.length;
  if (total < 2) return;

  // 如果基本上在完全淡出时，不创建新连接（节省性能并匹配视觉）
  if (fadeProgress < 0.04) return;

  // 使用一个局部 eased，用于使连接生成在淡入时更平滑（慢启动）
  const localEased = Math.pow(fadeProgress, 1.6); // 0..1, 较小进度时更小

  // chain extension attempts (scaled by localEased)
  let ops = 0;
  const baseTries = Math.min(Math.max(40, Math.floor(total * 0.35)), total);
  const tries = Math.max(6, Math.floor(baseTries * (0.35 + 0.65 * localEased))); // 起步更小，随fade增长
  const idxs = new Uint32Array(tries);
  for (let i = 0; i < tries; i++) idxs[i] = Math.floor(fnRnd() * total);

  for (let ii = 0; ii < tries && ops < maxChainOps && connections.length < maxTotalConnections; ii++) {
    const p = tempParticles[idxs[ii]];
    if (!p || p.bIsDead) continue;
    if (p._connCount >= maxDegree) continue;

    // find best candidate in hop band
    let best = null; let bestDistSq = Infinity;
    grid.forEachNeighbor(p, function(candidate) {
      if (candidate === p || candidate.bIsDead) return;
      if (candidate._connCount >= maxDegree) return;
      const dx = p.fProjX - candidate.fProjX;
      const dy = p.fProjY - candidate.fProjY;
      const dsq = dx*dx + dy*dy;
      if (dsq < minHopSq || dsq > maxHopSq) return;
      if (dsq < bestDistSq) { bestDistSq = dsq; best = candidate; }
    });

    if (best) {
      const key = makeConnKey(p._id, best._id);
      const now = Date.now();
      const existing = connMap.get(key);
      if (existing) {
        // potentiation proportional to fadeProgress (在凝聚时更明显)
        existing.weight = Math.min(1.5, existing.weight + 0.04 * (0.6 + 0.8 * localEased) + 0.03 * fnRnd());
        existing.life = Math.max(existing.life, Math.floor((6 + Math.floor(fnRnd() * 24)) * (0.5 + localEased)));
        existing.lastUsed = now;
        p.flashTimer = Math.max(p.flashTimer || 0, 8);
        best.flashTimer = Math.max(best.flashTimer || 0, 8);
        // 发散控制：如果处于高凝聚态则减少每次 potentiation 的 sparks 数量
        if (fadeProgress > 0.6) {
          spawnSparksAt(p.fProjX, p.fProjY, Math.max(1, Math.floor(3 * (1 - 0.35 * fadeProgress))));
          spawnSparksAt(best.fProjX, best.fProjY, Math.max(1, Math.floor(3 * (1 - 0.35 * fadeProgress))));
        } else if (fadeProgress > 0.3) {
          spawnSparksAt(p.fProjX, p.fProjY, 2);
          spawnSparksAt(best.fProjX, best.fProjY, 2);
        }
      } else {
        // create new connection object with initial weight scaled by fadeProgress
        const conn = {
          aId: p._id, bId: best._id, aRef: p, bRef: best,
          life: Math.max(2, Math.floor((6 + Math.floor(fnRnd() * 20)) * (0.5 + localEased))),
          createdAt: now,
          weight: Math.max(0.12, (0.4 + 0.6 * localEased) * (0.6 + 0.4 * fnRnd())),   // initial weight grows with fade
          lastUsed: now
        };
        connMap.set(key, conn);
        connections.push(conn);
        p._connCount++; best._connCount++;
        p.flashTimer = 8; best.flashTimer = 8;
        // spark 发散受凝聚态抑制（凝聚高时发散少）
        const sparkCount = Math.max(0, Math.floor(sparkSpawnOnFlash * (1 - 0.28 * fadeProgress)));
        if (sparkCount > 0 && fadeProgress > 0.25) spawnSparksAt(p.fProjX, p.fProjY, sparkCount);
        if (sparkCount > 0 && fadeProgress > 0.25) spawnSparksAt(best.fProjX, best.fProjY, sparkCount);
      }
      ops++;
    }
  }

  // random long-range links (small number) — reduce chance when fade low or condensed (to avoid excessive dispersion)
  let randCreated = 0;
  for (let r = 0; r < baseRandLinks * 3 && randCreated < baseRandLinks; r++) {
    if (fnRnd() > (0.15 + 0.6 * localEased)) continue; // only sometimes, more likely when localEased higher
    const a = tempParticles[Math.floor(fnRnd() * tempParticles.length)];
    const b = tempParticles[Math.floor(fnRnd() * tempParticles.length)];
    if (!a || !b || a === b) continue;
    if (a._connCount >= maxDegree || b._connCount >= maxDegree) continue;
    const key = makeConnKey(a._id, b._id);
    if (connMap.has(key)) {
      const c = connMap.get(key);
      // potentiate existing by a factor that depends on fadeProgress
      c.weight = Math.min(1.5, c.weight + 0.03 * (0.8 + localEased));
      c.life = Math.max(c.life, Math.floor((6 + Math.floor(fnRnd()*22)) * (0.5 + localEased)));
      c.lastUsed = Date.now();
      a.flashTimer = Math.max(a.flashTimer || 0, 7);
      b.flashTimer = Math.max(b.flashTimer || 0, 7);
      randCreated++;
      continue;
    }
    if (fnRnd() < 0.028 * (0.35 + 0.65 * localEased)) {
      const conn = {
        aId: a._id, bId: b._id, aRef: a, bRef: b,
        life: Math.max(2, Math.floor((6 + Math.floor(fnRnd()*28)) * (0.4 + localEased))),
        createdAt: Date.now(),
        weight: Math.min(1.2, 0.3 + 0.8 * fnRnd() * (0.5 + localEased)),
        lastUsed: Date.now()
      };
      connMap.set(key, conn);
      connections.push(conn);
      a._connCount++; b._connCount++;
      a.flashTimer = 7; b.flashTimer = 7;
      const sparkCount = Math.max(0, Math.floor(2 * (1 - 0.25 * fadeProgress)));
      if (sparkCount > 0 && fadeProgress > 0.25) { spawnSparksAt(a.fProjX, a.fProjY, sparkCount); spawnSparksAt(b.fProjX, b.fProjY, sparkCount); }
      randCreated++;
    }
  }
}

    // draw connections - MODIFIED without glow
function drawConnections(ctx) {
  if (connections.length === 0) return;
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < connections.length; i++) {
    const c = connections[i];
    if (!c.aRef || !c.bRef) continue;
    const p1 = c.aRef, p2 = c.bRef;
    const dx = p1.fProjX - p2.fProjX;
    const dy = p1.fProjY - p2.fProjY;
    const distSq = dx*dx + dy*dy;
    if (distSq > maxDistanceSq) continue; // skip very far

    // weight influences alpha/width but both modulated by fadeProgress
    const wgt = Math.min(1.4, c.weight || 0.4);
    // alpha 基于 weight，但乘以 fadeProgress（确保链随 fade 同步）
    const alphaBase = Math.max(0.05, 0.45 * wgt);
    const alpha = alphaBase * Math.min(1, Math.max(0, fadeProgress)); // 强制 0..1
    ctx.beginPath();
    // 线宽也随 fade 控制（fade 越低越细）
    ctx.lineWidth = (0.6 + 1.2 * wgt) * Math.max(0.18, fadeProgress);
    ctx.strokeStyle = `rgba(${window.aColor[0]},${window.aColor[1]},${window.aColor[2]},${alpha.toFixed(3)})`;
    ctx.moveTo(p1.fProjX, p1.fProjY);
    ctx.lineTo(p2.fProjX, p2.fProjY);
    ctx.stroke();
    ctx.closePath();
  }
  ctx.restore();
}

    // Spark system functions
function spawnSparksAt(x, y, count) {
  // 在凝聚态时适度减少发散：fadeProgress 越高，数量与速度越小（让凝聚更“紧凑”）
  const countScale = Math.max(0.35, 1.0 - 0.45 * fadeProgress); // 0.35..1.0
  const speedScale = Math.max(0.45, 1.0 - 0.45 * fadeProgress);
  const actualCount = Math.max(0, Math.floor(count * countScale));
  for (let i = 0; i < actualCount && sparks.length < maxSparks; i++) {
    const angle = fnRnd() * Math.PI * 2;
    const baseSpeed = 0.8 + fnRnd() * 2.6;
    const speed = baseSpeed * speedScale + (fadeProgress * 0.6 * (1 - speedScale)); // blend slightly
    sparks.push({
      x: x,
      y: y,
      vx: Math.cos(angle) * speed,
      vy: Math.sin(angle) * speed,
      life: 12 + Math.floor(fnRnd() * 22),
      alpha: 1.0,
      size: 0.6 + fnRnd() * 1.8
    });
  }
}

function updateSparks(dtMs) {
  for (let i = sparks.length - 1; i >= 0; i--) {
    const s = sparks[i];
    s.x += s.vx * (dtMs/16.6);
    s.y += s.vy * (dtMs/16.6);
    s.life--;
    s.alpha = Math.max(0, s.life / 30) * Math.max(0.25, fadeProgress); // sparks 的 alpha 也受 fadeProgress 影响
    if (s.life <= 0) sparks.splice(i, 1);
  }
}

    function drawSparks(ctx) {
      if (sparks.length === 0) return;
      ctx.save();
      ctx.globalCompositeOperation = 'lighter';
      for (let i = 0; i < sparks.length; i++) {
        const s = sparks[i];
        ctx.beginPath();
        ctx.fillStyle = `rgba(${window.aColor[0]},${window.aColor[1]},${window.aColor[2]},${(s.alpha * 0.66 * fadeProgress).toFixed(3)})`;
        ctx.arc(s.x, s.y, s.size, 0, Math.PI*2);
        ctx.fill();
        ctx.closePath();
      }
      ctx.restore();
    }

    fnRender = function() {
      // background
      ctxRender.fillStyle = "#000";
      ctxRender.fillRect(0, 0, w, h);

      // draw particles with flash effect - MODIFIED with highlight
      for (let p = oRender.pFirst; p != null; p = p.pNext) {
        let radiusMultiplier = 1.0;
        if (p.flashTimer && p.flashTimer > 0) {
          radiusMultiplier = 1.0 + 0.9 * (p.flashTimer / 8);
          p.flashTimer = Math.max(0, p.flashTimer - 1);
        }
        // 强调互联粒子（权重大或 highlight）
        if (p.highlight) radiusMultiplier *= 1.08 + Math.min(0.6, p._connCount * 0.25);
        const drawRadius = Math.max(0.35, p.fRadiusCurrent * radiusMultiplier);

        if (p.highlight) {
          ctxRender.fillStyle = `rgba(${Math.min(255,window.aColor[0]+40)}, ${Math.min(255,window.aColor[1]+40)}, ${Math.min(255,window.aColor[2]+40)}, ${(p.fAlpha * fadeProgress).toFixed(3)})`;
        } else {
          ctxRender.fillStyle = `rgba(${window.aColor[0]}, ${window.aColor[1]}, ${window.aColor[2]}, ${(p.fAlpha * fadeProgress * 0.78).toFixed(3)})`;
        }
        ctxRender.beginPath();
        ctxRender.arc(p.fProjX, p.fProjY, drawRadius, 0, 2*Math.PI);
        ctxRender.closePath();
        ctxRender.fill();
      }

      // draw connections above particles
      drawConnections(ctxRender);
      
      // draw sparks above connections
      drawSparks(ctxRender);
    };

    // time-tracking for delta
    let lastFrameTime = Date.now();

    // adaptive control: reduce spawn if dt large
    let adaptiveReduceUntil = 0;

    // Parameter update function - MODIFIED with easing
    function updateParams(progress) {
        // progress: 0..1 (fadeProgress)
        // We want view linear but other params to change more slowly at start:
        // use easedProgress = progress^2 (stronger slow-start). You can change exponent >1 for slower start.
        const eased = Math.pow(progress, 2.0); // slower ramp-up: small when progress small

        const paramMax = {
            iPerspective: 350,         // <= 350 锁定最大值
            fGrowDuration: 300,
            fWaitDuration: 100,
            iNewParticlePerFrame: 15
        };
        const paramMin = {
            iPerspective: 200,
            fGrowDuration: 50,
            fWaitDuration: 20,
            iNewParticlePerFrame: 3
        };

        // view (iPerspective) should be linear (not eased)
        window.iPerspective = Math.round(paramMin.iPerspective + (paramMax.iPerspective - paramMin.iPerspective) * progress);

        // Other params use eased (slower initial change)
        window.fGrowDuration = paramMin.fGrowDuration + (paramMax.fGrowDuration - paramMin.fGrowDuration) * eased;
        window.fWaitDuration = paramMin.fWaitDuration + (paramMax.fWaitDuration - paramMin.fWaitDuration) * eased;

        // particle/frame we keep integer and eased
        window.iNewParticlePerFrame = Math.max(1, Math.round(paramMin.iNewParticlePerFrame + (paramMax.iNewParticlePerFrame - paramMin.iNewParticlePerFrame) * eased));
    }

    fnNextFrame = function() {
      oStats.begin();
      const now = Date.now();
      const dtMs = Math.min(100, now - lastFrameTime); // clamp
      lastFrameTime = now;

      // mouse still detection (target fade)
      if (now - lastMouseMoveTime > mouseStillThresholdMs) {
        fadeTarget = 0.0;
      } else {
        fadeTarget = 1.0;
      }

      // time-based fade progression (FIX: use dt, not frames)
      if (fadeProgress < fadeTarget) {
        fadeProgress = Math.min(fadeTarget, fadeProgress + dtMs / fadeDurationMs);
      } else if (fadeProgress > fadeTarget) {
        fadeProgress = Math.max(fadeTarget, fadeProgress - dtMs / fadeDurationMs);
      }

      // RGB color cycling
      let t = now / 1000;
      window.aColor = [
          Math.floor(128 + 127 * Math.sin(t)),
          Math.floor(128 + 127 * Math.sin(t + 2)),
          Math.floor(128 + 127 * Math.sin(t + 4))
      ];

      // Update interpolated params
      updateParams(fadeProgress);

      // adaptive protection based on dt
      if (dtMs > 40) { // <25 FPS
        adaptiveReduceUntil = now + 700; // for next 700ms reduce
      }
      const adaptiveFactor = (now < adaptiveReduceUntil) ? 0.5 : 1.0;

      // rotation update
      fAngle = (fAngle + fVX) % (2.0 * fPI);
      fSinAngle = fnSin(fAngle);
      fCosAngle = fnCos(fAngle);

      // spawn new particles (clamp and adapt)
      let spawnCount = Math.max(1, Math.round(window.iNewParticlePerFrame * adaptiveFactor));
      spawnCount = Math.min(20, spawnCount);
      let iAddParticle = 0;
      while (iAddParticle++ < spawnCount) {
        const p = fnSwapList(oBuffer.pFirst, oBuffer, oRender);
        p.fnInit();
      }

    // update particles and collect active ones into tempParticles (reused)
    collectParticles(oRender, tempParticles);
    
    // Smooth transition of particle durations to match current window values
    const durLerp = 0.12; // 0.0..1.0, higher means faster change (recommended 0.08..0.18)
    for (let j = 0; j < tempParticles.length; j++) {
      const p = tempParticles[j];
      p.fGrowDuration += (window.fGrowDuration - p.fGrowDuration) * durLerp;
      p.fWaitDuration += (window.fWaitDuration - p.fWaitDuration) * durLerp;
      p.fShrinkDuration += (window.fShrinkDuration - p.fShrinkDuration) * durLerp;
    }
    
    for (let idx = 0; idx < tempParticles.length; idx++) {
      tempParticles[idx].fnUpdate();
    }

      // prepare grid
      grid.clear();
      // allocate grid rows lazily; insertion will clamp coords
      for (let i = 0; i < tempParticles.length; i++) {
        grid.insert(tempParticles[i]);
      }

      // manage connections: prune, create (local + random)
      pruneConnectionsAndReveal();
      createConnections();

      // update sparks
      updateSparks(dtMs);

      // render everything
      fnRender();

      oStats.end();
      return fnRequestAnimationFrame(fnNextFrame);
    };

    fnNextFrame();

    // GUI (optional)
    window.app = this;
  };

  fnAddEventListener(window, 'load', app);
}).call(this);

function livelyPropertyListener(name, val)
{
  switch(name) {
  case "fGrowDuration":
      window.fGrowDuration = val;
    break;
  case "fWaitDuration":
      window.fWaitDuration = val;
    break;
  case "fShrinkDuration":
      window.fShrinkDuration = val;
    break;
  case "iPerspective":
      window.iPerspective = val;
    break;
  case "iNewParticlePerFrame":
      window.iNewParticlePerFrame = val;
  break;
  case "iFramesToRotate":
      window.iFramesToRotate = val;
      // NOTE: fVX is local inside app(); changing this here won't affect running instance.
  break;
  case "aColor":
      var tmpColor = hexToRgb(val);
      if (tmpColor) {
        window.aColor[0] = tmpColor.r;
        window.aColor[1] = tmpColor.g;
        window.aColor[2] = tmpColor.b;
      }
  break;
  }
}

function hexToRgb(hex) {
  var result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  return result ? {
    r: parseInt(result[1], 16),
    g: parseInt(result[2], 16),
    b: parseInt(result[3], 16)
  } : null;
}
