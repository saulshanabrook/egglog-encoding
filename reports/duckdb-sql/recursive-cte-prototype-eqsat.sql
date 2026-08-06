-- Provenance: recursive-CTE feasibility prototype built 2026-08-05 by a claude
-- sub-agent (session 'duckdb review' #2); preserved from
-- ~/p/wt/egglog-encoding-duckdb-recursive-cte-prototype/eqsat_final.sql.
-- Runs on stock DuckDB >= 1.3: duckdb < this-file. Expected output:
-- PROVED: (a*2)/2 == a | ~10 waves | 0.19s. See reports/duckdb-sql/recursive-cte-plan.md.
-- ============================================================================
-- Equality saturation in ONE DuckDB recursive CTE (no host code between waves).
-- Mirrors egg's classic intro example / egglog eqsat-basic style program:
--   seed:  (Div (Mul (Var a) (Num 2)) (Num 2))
--   rules: (Mul x y) -> (Mul y x)
--          (Div (Mul x y) z) -> (Mul x (Div y z))
--          (Div x x) -> (Num 1)
--          (Mul x (Num 1)) -> x
--   check: class((a*2)/2) == class(a)
--
-- State = one keyed relation, key (tag, op, a, b), payload (x, live):
--   ('uf','',id,0)     x = current leader (min known member id of its class)
--   ('e', op,c1,c2)    x = eclass id; live=false => tombstoned (rekeyed away)
--   ('edge','',p,q)    persistent union fact (classes p and q are equal)
--   ('ctl','',0,0)     x = wave counter
--
-- Rule waves are capped at 10 (this rule system does NOT saturate: reassoc +
-- commutativity legitimately generate a/2, (a/2)/2, ... forever, which is why
-- egg/egglog bound iterations). After the rule cap, congruence closure, UF
-- min-propagation and canonicalization keep running to their own fixpoint
-- (egglog's "rebuild"), which IS finite. Safety cap 500 guards everything.
-- ============================================================================
WITH RECURSIVE state USING KEY (tag, op, a, b) AS (
  SELECT * FROM (VALUES
    ('uf','',1::BIGINT,0::BIGINT,1::BIGINT,true),
    ('uf','',2,0,2,true),
    ('uf','',3,0,3,true),
    ('uf','',4,0,4,true),
    ('e','var:a',0,0,1,true),
    ('e','num:2',0,0,2,true),
    ('e','mul',1,2,3,true),
    ('e','div',3,2,4,true),
    ('ctl','',0,0,0,true)
  ) v(tag, op, a, b, x, live)
  UNION ALL
  (
    WITH
    itc AS (SELECT x AS i FROM recurring.state WHERE tag='ctl'),
    uf AS (SELECT a AS id, x AS l FROM recurring.state WHERE tag='uf'),
    edges AS (SELECT a AS p, b AS q FROM recurring.state WHERE tag='edge'),
    en AS (SELECT op, a, b, x, live FROM recurring.state WHERE tag='e'),
    -- canonical view of live enodes (children/class via current leaders)
    cn AS (
      SELECT e.op,
             CASE WHEN e.a=0 THEN 0 ELSE la.l END AS ca,
             CASE WHEN e.b=0 THEN 0 ELSE lb.l END AS cb,
             lc.l AS cc,
             e.a AS ra, e.b AS rb
      FROM en e
      LEFT JOIN uf la ON la.id = e.a
      LEFT JOIN uf lb ON lb.id = e.b
      JOIN uf lc ON lc.id = e.x
      WHERE e.live
    ),
    grp AS (SELECT op, ca, cb, min(cc) AS g FROM cn GROUP BY op, ca, cb),
    -- congruence closure: same op + same canonical children => same class
    cong_edges AS (
      SELECT least(c.cc, g.g) AS p, greatest(c.cc, g.g) AS q
      FROM cn c JOIN grp g ON g.op=c.op AND g.ca=c.ca AND g.cb=c.cb
      WHERE c.cc <> g.g
    ),
    grp_status AS (
      SELECT g.op, g.ca, g.cb, g.g, e.x AS ex_x, e.live AS ex_live, ue.l AS ex_l
      FROM grp g
      LEFT JOIN en e ON e.op=g.op AND e.a=g.ca AND e.b=g.cb
      LEFT JOIN uf ue ON ue.id = e.x
    ),
    -- hashcons upsert of the canonical enode row (never resurrect a tombstone)
    grp_intents AS (
      SELECT op, ca AS a, cb AS b, g AS x FROM grp_status
      WHERE ex_x IS NULL OR (ex_live AND g < ex_x)
    ),
    exist_edges AS (
      SELECT least(ex_l, g) AS p, greatest(ex_l, g) AS q
      FROM grp_status WHERE ex_x IS NOT NULL AND ex_l <> g
    ),
    -- rekey: stale-keyed live row dies (unless its key is this wave's canonical
    -- target for some group, which would collide; it dies a wave later instead)
    tombstones AS (
      SELECT c.op, c.ra AS a, c.rb AS b, c.cc AS x
      FROM cn c
      WHERE (c.ca <> c.ra OR c.cb <> c.rb)
        AND NOT EXISTS (SELECT 1 FROM grp g
                        WHERE g.op=c.op AND g.ca=c.ra AND g.cb=c.rb)
    ),
    ---------------- rewrite rules (gated by rule-wave cap 10) ----------------
    r1 AS ( -- (Mul x y) -> (Mul y x)
      SELECT 'mul' AS op, cb AS a, ca AS b, cc AS t
      FROM cn, itc WHERE op='mul' AND itc.i < 10
    ),
    r2m AS ( -- (Div (Mul x y) z) matches
      SELECT m.ca AS xx, m.cb AS yy, d.cb AS zz, d.cc AS t
      FROM cn d JOIN cn m ON m.op='mul' AND m.cc = d.ca
      CROSS JOIN itc
      WHERE d.op='div' AND itc.i < 10
    ),
    -- (Div y z) must exist: reuse by exact key (live or dead) or by canonical
    -- group; otherwise mint a fresh eclass id deterministically
    inner_want AS (SELECT DISTINCT 'div' AS op, yy AS a, zz AS b FROM r2m),
    inner_lookup AS (
      SELECT w.op, w.a, w.b, coalesce(ue.l, g.g) AS cls
      FROM inner_want w
      LEFT JOIN en e ON e.op=w.op AND e.a=w.a AND e.b=w.b
      LEFT JOIN uf ue ON ue.id = e.x
      LEFT JOIN grp g ON g.op=w.op AND g.ca=w.a AND g.cb=w.b
    ),
    minted AS (
      SELECT op, a, b,
             (SELECT max(id) FROM uf) + dense_rank() OVER (ORDER BY op, a, b) AS cls
      FROM inner_lookup WHERE cls IS NULL
    ),
    inner_resolved AS (
      SELECT op, a, b, cls FROM inner_lookup WHERE cls IS NOT NULL
      UNION ALL
      SELECT op, a, b, cls FROM minted
    ),
    r3 AS ( -- (Div x x) -> (Num 1)
      SELECT 'num:1' AS op, 0::BIGINT AS a, 0::BIGINT AS b, cc AS t
      FROM cn, itc WHERE op='div' AND ca = cb AND itc.i < 10
    ),
    r4_edges AS ( -- (Mul x (Num 1)) -> x   [pure union]
      SELECT least(m.cc, m.ca) AS p, greatest(m.cc, m.ca) AS q
      FROM cn m JOIN cn n ON n.op='num:1' AND n.cc = m.cb
      CROSS JOIN itc
      WHERE m.op='mul' AND m.cc <> m.ca AND itc.i < 10
    ),
    wants AS (  -- enode (op,a,b) should exist and live in class t
      SELECT op, a, b, t FROM r1
      UNION ALL
      SELECT 'mul', r.xx, ir.cls, r.t
      FROM r2m r JOIN inner_resolved ir ON ir.a = r.yy AND ir.b = r.zz
      UNION ALL
      SELECT op, a, b, t FROM r3
    ),
    want_agg AS (SELECT op, a, b, min(t) AS mt FROM wants GROUP BY op, a, b),
    want_status AS (
      SELECT w.op, w.a, w.b, w.mt, e.x AS ex_x, ue.l AS ex_l, g.g
      FROM want_agg w
      LEFT JOIN en e ON e.op=w.op AND e.a=w.a AND e.b=w.b
      LEFT JOIN uf ue ON ue.id = e.x
      LEFT JOIN grp g ON g.op=w.op AND g.ca=w.a AND g.cb=w.b
    ),
    want_new_rows AS ( -- hashcons miss: brand-new enode
      SELECT op, a, b, mt AS x FROM want_status WHERE ex_x IS NULL AND g IS NULL
    ),
    want_edges AS (    -- hashcons hit: union target class with existing class
      SELECT least(coalesce(ex_l, g), mt) AS p, greatest(coalesce(ex_l, g), mt) AS q
      FROM want_status
      WHERE coalesce(ex_l, g) IS NOT NULL AND coalesce(ex_l, g) <> mt
      UNION ALL
      SELECT min(t), max(t) FROM wants GROUP BY op, a, b HAVING min(t) <> max(t)
    ),
    ---------------- assembly (same-key collisions resolved here) -------------
    live_src AS (
      SELECT op, a, b, x FROM grp_intents
      UNION ALL SELECT op, a, b, x FROM want_new_rows
      UNION ALL SELECT op, a, b, cls FROM minted
    ),
    assembled AS (
      SELECT op, a, b, min(x) AS x, bool_and(live) AS live
      FROM (
        SELECT op, a, b, x, true AS live FROM live_src
        UNION ALL SELECT op, a, b, x, false FROM tombstones
      ) GROUP BY op, a, b
    ),
    conflict_edges AS (
      SELECT min(x) AS p, max(x) AS q
      FROM live_src GROUP BY op, a, b HAVING min(x) <> max(x)
    ),
    new_edges AS (
      SELECT DISTINCT p, q FROM (
        SELECT p, q FROM cong_edges
        UNION ALL SELECT p, q FROM exist_edges
        UNION ALL SELECT p, q FROM r4_edges
        UNION ALL SELECT p, q FROM want_edges
        UNION ALL SELECT p, q FROM conflict_edges
      ) ne
      WHERE p <> q AND NOT EXISTS (SELECT 1 FROM edges e WHERE e.p=ne.p AND e.q=ne.q)
    ),
    -- UF: leader(x) := min(leader(leader(x)), leaders across union edges)
    uf_cand AS (
      SELECT u.id, u2.l AS nl FROM uf u JOIN uf u2 ON u2.id = u.l
      UNION ALL SELECT e.p, u.l FROM edges e JOIN uf u ON u.id = e.q
      UNION ALL SELECT e.q, u.l FROM edges e JOIN uf u ON u.id = e.p
    ),
    uf_upd AS (
      SELECT c.id, min(c.nl) AS nl
      FROM uf_cand c JOIN uf u ON u.id = c.id
      GROUP BY c.id, u.l HAVING min(c.nl) < u.l
    ),
    chg AS (
      SELECT (SELECT count(*) FROM assembled) + (SELECT count(*) FROM new_edges)
           + (SELECT count(*) FROM uf_upd) + (SELECT count(*) FROM minted) AS n
    )
    -- every branch is guarded against no-ops; safety cap 500 on everything
    SELECT 'uf' AS tag, '' AS op, id AS a, 0::BIGINT AS b, nl AS x, true AS live
      FROM uf_upd, itc WHERE itc.i < 500
    UNION ALL
    SELECT 'uf', '', cls, 0, cls, true FROM minted, itc WHERE itc.i < 500
    UNION ALL
    SELECT 'e', op, a, b, x, live FROM assembled, itc WHERE itc.i < 500
    UNION ALL
    SELECT 'edge', '', p, q, 0, true FROM new_edges, itc WHERE itc.i < 500
    UNION ALL
    SELECT 'ctl', '', 0, 0, itc.i + 1, true FROM itc, chg WHERE chg.n > 0 AND itc.i < 500
  )
)
SELECT
  CASE WHEN (SELECT x FROM state WHERE tag='uf' AND a=4)
          = (SELECT x FROM state WHERE tag='uf' AND a=1)
       THEN 'PROVED: (a*2)/2 == a in class '
            || (SELECT x FROM state WHERE tag='uf' AND a=1)
       ELSE error('CHECK FAILED: (a*2)/2 not equal to a') END AS result,
  (SELECT x FROM state WHERE tag='ctl')                        AS waves,
  (SELECT count(*) FROM state WHERE tag='e' AND live)          AS live_enodes,
  (SELECT count(*) FROM state WHERE tag='e' AND NOT live)      AS tombstoned,
  (SELECT count(*) FROM state WHERE tag='uf')                  AS eclass_ids,
  (SELECT count(*) FROM state WHERE tag='edge')                AS union_edges,
  (SELECT count(DISTINCT x) FROM state WHERE tag='uf')         AS canonical_classes;
