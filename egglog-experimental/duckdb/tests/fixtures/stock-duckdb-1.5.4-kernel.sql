-- Stock DuckDB 1.5.4 capability fixture for the generic merge kernel.
--
-- This file is deliberately independent of the Rust DuckDB API.  The checker
-- runs it in a safe, in-memory stock CLI and requires every assertion below to
-- return exactly one {"test": ..., "status": "ok"} row.  Keep the fixture
-- free of configuration statements: ordering comes from explicit semantic
-- keys and source ordinals, never connection settings.

-- A keyed recurrence preserves concrete nested LIST/STRUCT types, including a
-- hostile string which looks like SQL to a textual scanner.
WITH RECURSIVE typed_nested(key, payload) USING KEY (key) AS (
    (
        SELECT
            1::UBIGINT,
            struct_pack(
                path := [1::UBIGINT],
                proof := struct_pack(
                    id := 100::UBIGINT,
                    parents := [10::UBIGINT, 11::UBIGINT]
                ),
                note := 'quote ''; -- /* */ SET threads = 9; ' || chr(10)
                    || 'snowman ☃ \ slash'
            )
    )
    UNION ALL
    (
        SELECT
            key + 1,
            struct_pack(
                path := list_append(payload.path, key + 1),
                proof := struct_pack(
                    id := payload.proof.id + 1,
                    parents := list_append(payload.proof.parents, key + 1)
                ),
                note := payload.note
            )
        FROM typed_nested
        WHERE key < 3
    )
)
SELECT
    'typed_nested_using_key' AS test,
    CASE
        WHEN count(*) = 3
            AND max_by(payload.path, key) = [1::UBIGINT, 2::UBIGINT, 3::UBIGINT]
            AND max_by(payload.proof.id, key) = 102::UBIGINT
            AND max_by(payload.proof.parents, key)
                = [10::UBIGINT, 11::UBIGINT, 2::UBIGINT, 3::UBIGINT]
            AND bool_and(
                payload.note IS NOT DISTINCT FROM 'quote ''; -- /* */ SET threads = 9; ' || chr(10)
                    || 'snowman ☃ \ slash'
            )
        THEN 'ok'
        ELSE error('typed nested USING KEY assertion failed')
    END AS status
FROM typed_nested;

-- Zero references to the working table are legal.  Strict anti-diff against
-- the recurring snapshot makes the recurrence naturally produce no row at
-- the fixed point instead of relying on an engine recursion limit.
WITH RECURSIVE recurring_only(key, value) USING KEY (key) AS (
    (VALUES (1::UBIGINT, 0::UBIGINT))
    UNION ALL
    (
        SELECT prior.key, least(prior.value + 1, 3::UBIGINT)
        FROM recurring.recurring_only AS prior
        WHERE prior.key = 1
          AND least(prior.value + 1, 3::UBIGINT) IS DISTINCT FROM prior.value
    )
)
SELECT
    'recurring_only_strict_antidiff' AS test,
    CASE
        WHEN count(*) = 1 AND max(value) = 3::UBIGINT
        THEN 'ok'
        ELSE error('recurring-only anti-diff assertion failed')
    END AS status
FROM recurring_only;

-- Exactly one working-table source drives each seminaive wave.  Two separate
-- recurring reads see the full accumulated snapshot, not just that wave.
WITH RECURSIVE seminaive(key, left_snapshot, right_snapshot) USING KEY (key) AS (
    (VALUES (0::BIGINT, 0::BIGINT, 0::BIGINT))
    UNION ALL
    (
        SELECT
            working.key + 1,
            (SELECT count(*)::BIGINT FROM recurring.seminaive),
            (
                SELECT count(*)::BIGINT
                FROM recurring.seminaive AS right_snapshot
                WHERE right_snapshot.key <= working.key
            )
        FROM seminaive AS working
        WHERE working.key < 3
    )
)
SELECT
    'one_working_multiple_recurring' AS test,
    CASE
        WHEN count(*) = 4
            AND count(*) FILTER (
                WHERE key = 1 AND left_snapshot = 1 AND right_snapshot = 1
            ) = 1
            AND count(*) FILTER (
                WHERE key = 2 AND left_snapshot = 2 AND right_snapshot = 2
            ) = 1
            AND count(*) FILTER (
                WHERE key = 3 AND left_snapshot = 3 AND right_snapshot = 3
            ) = 1
        THEN 'ok'
        ELSE error('working/recurring cardinality assertion failed')
    END AS status
FROM seminaive;

-- Candidates sharing a key are folded in explicit source order before keyed
-- emission.  The kernel must never use USING KEY's last-row replacement as a
-- duplicate-key fold.
WITH RECURSIVE source_events(key, source_ordinal, amount, payload) AS (
    VALUES
        (1::UBIGINT, 2::UBIGINT, 30::BIGINT, 'line' || chr(10) || 'snowman ☃'),
        (1::UBIGINT, 0::UBIGINT, 10::BIGINT, 'quote '' and ; -- text'),
        (1::UBIGINT, 1::UBIGINT, 20::BIGINT, '/* text */ SET x = 1; \ slash'),
        (2::UBIGINT, 1::UBIGINT, 7::BIGINT, 'second-b'),
        (2::UBIGINT, 0::UBIGINT, 5::BIGINT, 'second-a')
),
folded AS (
    SELECT
        key,
        list(source_ordinal ORDER BY source_ordinal) AS source_order,
        list(payload ORDER BY source_ordinal) AS payload_order,
        list_reduce(
            list(amount ORDER BY source_ordinal),
            lambda total, next_amount: total + next_amount
        ) AS total,
        list_reduce(
            list(amount::VARCHAR ORDER BY source_ordinal),
            lambda prefix, next_amount: prefix || '>' || next_amount
        ) AS fold_digest
    FROM source_events
    GROUP BY key
),
keyed_fold(key, source_order, payload_order, total, fold_digest) USING KEY (key) AS (
    (
        SELECT key, source_order, payload_order, total, fold_digest
        FROM folded
    )
    UNION ALL
    (
        SELECT key, source_order, payload_order, total, fold_digest
        FROM keyed_fold
        WHERE FALSE
    )
)
SELECT
    'deterministic_duplicate_fold' AS test,
    CASE
        WHEN count(*) = 2
            AND count(*) FILTER (
                WHERE key = 1
                  AND source_order = [0::UBIGINT, 1::UBIGINT, 2::UBIGINT]
                  AND payload_order = [
                      'quote '' and ; -- text',
                      '/* text */ SET x = 1; \ slash',
                      'line' || chr(10) || 'snowman ☃'
                  ]
                  AND total = 60
                  AND fold_digest = '10>20>30'
            ) = 1
            AND count(*) FILTER (
                WHERE key = 2
                  AND source_order = [0::UBIGINT, 1::UBIGINT]
                  AND payload_order = ['second-a', 'second-b']
                  AND total = 12
                  AND fold_digest = '5>7'
            ) = 1
        THEN 'ok'
        ELSE error('deterministic duplicate fold assertion failed')
    END AS status
FROM keyed_fold;

-- Parentheses make the anchor, recursive term, and both lateral branches
-- unambiguous while retaining a single working-table reference.
WITH RECURSIVE multibranch(key, path) USING KEY (key) AS (
    (VALUES (0::UBIGINT, [0::UBIGINT]))
    UNION ALL
    (
        SELECT emitted.key, emitted.path
        FROM multibranch AS working
        CROSS JOIN LATERAL (
            (
                SELECT
                    working.key + 1 AS key,
                    list_append(working.path, working.key + 1) AS path
                WHERE working.key = 0
            )
            UNION ALL
            (
                SELECT
                    working.key + 2 AS key,
                    list_append(working.path, working.key + 2) AS path
                WHERE working.key = 0
            )
        ) AS emitted
    )
)
SELECT
    'fully_parenthesized_multibranch' AS test,
    CASE
        WHEN count(*) = 3
            AND count(*) FILTER (WHERE key = 1 AND path = [0::UBIGINT, 1::UBIGINT]) = 1
            AND count(*) FILTER (WHERE key = 2 AND path = [0::UBIGINT, 2::UBIGINT]) = 1
        THEN 'ok'
        ELSE error('fully parenthesized multibranch assertion failed')
    END AS status
FROM multibranch;

-- DuckDB rejects an empty USING KEY list.  A non-null Boolean is the typed
-- surrogate for a logically nullary controller relation.
WITH RECURSIVE nullary_controller(unit, ticks) USING KEY (unit) AS (
    (VALUES (TRUE, 0::UBIGINT))
    UNION ALL
    (
        SELECT TRUE, ticks + 1
        FROM nullary_controller
        WHERE ticks < 3
    )
)
SELECT
    'nullary_surrogate_key' AS test,
    CASE
        WHEN count(*) = 1 AND bool_and(unit) AND max(ticks) = 3::UBIGINT
        THEN 'ok'
        ELSE error('nullary surrogate assertion failed')
    END AS status
FROM nullary_controller;

-- A tombstone remains explicit data.  Delete, reinsert, then subsume are three
-- source-ordered events; omission from a recurring wave is never treated as a
-- physical delete.
WITH RECURSIVE lifecycle(
    kind,
    id,
    value,
    tombstoned,
    subsumed,
    step,
    history
) USING KEY (kind, id) AS (
    (
        VALUES
            (
                0::UTINYINT,
                1::UBIGINT,
                10::BIGINT,
                FALSE,
                FALSE,
                0::UBIGINT,
                []::STRUCT(
                    source_ordinal UBIGINT,
                    action VARCHAR,
                    value BIGINT,
                    tombstoned BOOLEAN,
                    subsumed BOOLEAN
                )[]
            ),
            (
                0::UTINYINT,
                2::UBIGINT,
                30::BIGINT,
                FALSE,
                FALSE,
                0::UBIGINT,
                []::STRUCT(
                    source_ordinal UBIGINT,
                    action VARCHAR,
                    value BIGINT,
                    tombstoned BOOLEAN,
                    subsumed BOOLEAN
                )[]
            ),
            (
                9::UTINYINT,
                0::UBIGINT,
                0::BIGINT,
                FALSE,
                FALSE,
                0::UBIGINT,
                []::STRUCT(
                    source_ordinal UBIGINT,
                    action VARCHAR,
                    value BIGINT,
                    tombstoned BOOLEAN,
                    subsumed BOOLEAN
                )[]
            )
    )
    UNION ALL
    (
        SELECT emitted.*
        FROM recurring.lifecycle AS controller
        CROSS JOIN recurring.lifecycle AS owner
        CROSS JOIN LATERAL (
            SELECT
                CASE WHEN controller.step = 1 THEN 20::BIGINT ELSE owner.value END AS value,
                CASE
                    WHEN controller.step = 0 THEN TRUE
                    WHEN controller.step = 1 THEN FALSE
                    ELSE owner.tombstoned
                END AS tombstoned,
                owner.subsumed OR controller.step = 2 AS subsumed
        ) AS transition
        CROSS JOIN LATERAL (
            (
                SELECT
                    0::UTINYINT AS kind,
                    1::UBIGINT AS id,
                    transition.value,
                    transition.tombstoned,
                    transition.subsumed,
                    controller.step + 1 AS step,
                    list_append(
                        owner.history,
                        struct_pack(
                            source_ordinal := controller.step + 1,
                            action := CASE controller.step
                                WHEN 0 THEN 'Delete'
                                WHEN 1 THEN 'Set'
                                ELSE 'Subsume'
                            END,
                            value := transition.value,
                            tombstoned := transition.tombstoned,
                            subsumed := transition.subsumed
                        )
                    ) AS history
            )
            UNION ALL
            (
                SELECT
                    9::UTINYINT,
                    0::UBIGINT,
                    0::BIGINT,
                    FALSE,
                    FALSE,
                    controller.step + 1,
                    controller.history
            )
        ) AS emitted
        WHERE controller.kind = 9
          AND owner.kind = 0 AND owner.id = 1
          AND controller.step < 3
    )
)
SELECT
    'tombstone_reinsert_subsume' AS test,
    CASE
        WHEN count(*) = 3
            AND count(*) FILTER (
                WHERE kind = 0 AND id = 1 AND value = 20
                  AND NOT tombstoned AND subsumed AND step = 3
                  AND history = [
                      struct_pack(
                          source_ordinal := 1::UBIGINT,
                          action := 'Delete',
                          value := 10::BIGINT,
                          tombstoned := TRUE,
                          subsumed := FALSE
                      ),
                      struct_pack(
                          source_ordinal := 2::UBIGINT,
                          action := 'Set',
                          value := 20::BIGINT,
                          tombstoned := FALSE,
                          subsumed := FALSE
                      ),
                      struct_pack(
                          source_ordinal := 3::UBIGINT,
                          action := 'Subsume',
                          value := 20::BIGINT,
                          tombstoned := FALSE,
                          subsumed := TRUE
                      )
                  ]
            ) = 1
            AND count(*) FILTER (
                WHERE kind = 0 AND id = 2 AND value = 30
                  AND NOT tombstoned AND NOT subsumed AND step = 0
                  AND len(history) = 0
            ) = 1
            AND count(*) FILTER (
                WHERE kind = 9 AND id = 0 AND step = 3 AND len(history) = 0
            ) = 1
        THEN 'ok'
        ELSE error('tombstone/reinsert/subsumption assertion failed')
    END AS status
FROM lifecycle;

-- Repeat uses a data limit, so N=0, N=1, and N=100000 differ only in literal
-- rows rather than SQL shape.  Saturate executes its child at least once even
-- when the first child report is already unchanged.
WITH RECURSIVE schedule_controller(
    case_id,
    mode,
    repeat_limit,
    child_calls,
    aggregate_updated,
    aggregate_can_stop,
    last_updated,
    last_can_stop,
    done
) USING KEY (case_id) AS (
    (
        VALUES
            (0::UTINYINT, 'repeat', 0::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, TRUE),
            (1::UTINYINT, 'repeat', 1::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, FALSE),
            (2::UTINYINT, 'repeat', 100000::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, FALSE),
            (3::UTINYINT, 'saturate', 0::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, FALSE),
            (4::UTINYINT, 'repeat_stop', 100000::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, FALSE),
            (5::UTINYINT, 'repeat_ff', 100000::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, FALSE),
            (6::UTINYINT, 'saturate_ff', 0::UBIGINT, 0::UBIGINT, FALSE, TRUE, FALSE, TRUE, FALSE)
    )
    UNION ALL
    (
        SELECT
            case_id,
            mode,
            repeat_limit,
            child_calls + 1,
            aggregate_updated OR mode = 'repeat',
            aggregate_can_stop AND CASE mode
                WHEN 'repeat' THEN FALSE
                WHEN 'repeat_stop' THEN TRUE
                WHEN 'repeat_ff' THEN child_calls >= 1
                WHEN 'saturate' THEN TRUE
                WHEN 'saturate_ff' THEN FALSE
                ELSE error('unknown schedule controller mode')::BOOLEAN
            END,
            mode = 'repeat',
            CASE mode
                WHEN 'repeat' THEN FALSE
                WHEN 'repeat_stop' THEN TRUE
                WHEN 'repeat_ff' THEN child_calls >= 1
                WHEN 'saturate' THEN TRUE
                WHEN 'saturate_ff' THEN FALSE
                ELSE error('unknown schedule controller mode')::BOOLEAN
            END,
            CASE
                WHEN mode IN ('repeat', 'repeat_stop', 'repeat_ff')
                    THEN child_calls + 1 >= repeat_limit OR CASE mode
                        WHEN 'repeat' THEN FALSE
                        WHEN 'repeat_stop' THEN TRUE
                        WHEN 'repeat_ff' THEN child_calls >= 1
                        ELSE error('unknown Repeat controller mode')::BOOLEAN
                    END
                ELSE NOT (mode = 'repeat')
            END
        FROM schedule_controller
        WHERE NOT done
    )
)
SELECT
    'repeat_and_first_saturate_iteration' AS test,
    CASE
        WHEN count(*) = 7
            AND count(*) FILTER (
                WHERE case_id = 0 AND child_calls = 0
                  AND NOT aggregate_updated AND aggregate_can_stop
            ) = 1
            AND count(*) FILTER (
                WHERE case_id = 1 AND child_calls = 1
                  AND aggregate_updated AND NOT aggregate_can_stop
            ) = 1
            AND count(*) FILTER (
                WHERE case_id = 2 AND child_calls = 100000
                  AND aggregate_updated AND NOT aggregate_can_stop
            ) = 1
            AND count(*) FILTER (
                WHERE case_id = 3 AND child_calls = 1
                  AND NOT aggregate_updated AND aggregate_can_stop
            ) = 1
            AND count(*) FILTER (
                WHERE case_id = 4 AND repeat_limit = 100000 AND child_calls = 1
                  AND NOT aggregate_updated AND aggregate_can_stop
                  AND NOT last_updated AND last_can_stop
            ) = 1
            AND count(*) FILTER (
                WHERE case_id = 5 AND repeat_limit = 100000 AND child_calls = 2
                  AND NOT aggregate_updated AND NOT aggregate_can_stop
                  AND NOT last_updated AND last_can_stop
            ) = 1
            AND count(*) FILTER (
                WHERE case_id = 6 AND child_calls = 1
                  AND NOT aggregate_updated AND NOT aggregate_can_stop
                  AND NOT last_updated AND NOT last_can_stop
            ) = 1
        THEN 'ok'
        ELSE error('Repeat/Saturate controller assertion failed')
    END AS status
FROM schedule_controller;

-- An inner Saturate stops on its last child's updated=false, while its returned
-- report remains aggregate_updated=true and aggregate_can_stop=false.  The
-- enclosing Repeat therefore executes both requested inner runs.
WITH RECURSIVE nested_controller(
    unit,
    outer_limit,
    outer_completed,
    inner_iteration,
    child_calls,
    inner_aggregate_updated,
    inner_aggregate_can_stop,
    outer_aggregate_updated,
    outer_aggregate_can_stop,
    last_child_updated,
    last_child_can_stop,
    done
) USING KEY (unit) AS (
    (
        VALUES (
            TRUE,
            2::UBIGINT,
            0::UBIGINT,
            0::UBIGINT,
            0::UBIGINT,
            FALSE,
            TRUE,
            FALSE,
            TRUE,
            FALSE,
            TRUE,
            FALSE
        )
    )
    UNION ALL
    (
        SELECT
            TRUE,
            working.outer_limit,
            transition.next_outer_completed,
            CASE
                WHEN transition.inner_done AND NOT transition.outer_done THEN 0::UBIGINT
                ELSE working.inner_iteration + 1
            END,
            working.child_calls + 1,
            CASE
                WHEN transition.inner_done AND NOT transition.outer_done THEN FALSE
                ELSE transition.returned_updated
            END,
            CASE
                WHEN transition.inner_done AND NOT transition.outer_done THEN TRUE
                ELSE transition.returned_can_stop
            END,
            CASE
                WHEN transition.inner_done
                    THEN working.outer_aggregate_updated OR transition.returned_updated
                ELSE working.outer_aggregate_updated
            END,
            CASE
                WHEN transition.inner_done
                    THEN working.outer_aggregate_can_stop AND transition.returned_can_stop
                ELSE working.outer_aggregate_can_stop
            END,
            child.updated,
            child.can_stop,
            transition.outer_done
        FROM nested_controller AS working
        CROSS JOIN LATERAL (
            SELECT
                working.inner_iteration = 0 AS updated,
                working.inner_iteration <> 0 AS can_stop
        ) AS child
        CROSS JOIN LATERAL (
            SELECT
                working.inner_aggregate_updated OR child.updated AS returned_updated,
                working.inner_aggregate_can_stop AND child.can_stop AS returned_can_stop,
                NOT child.updated AS inner_done,
                working.outer_completed + CASE WHEN NOT child.updated THEN 1 ELSE 0 END
                    AS next_outer_completed
        ) AS inner_report
        CROSS JOIN LATERAL (
            SELECT
                inner_report.returned_updated,
                inner_report.returned_can_stop,
                inner_report.inner_done,
                inner_report.next_outer_completed,
                inner_report.inner_done
                    AND (
                        inner_report.next_outer_completed >= working.outer_limit
                        OR inner_report.returned_can_stop
                    ) AS outer_done
        ) AS transition
        WHERE NOT working.done
    )
)
SELECT
    'nested_last_child_vs_aggregate_flags' AS test,
    CASE
        WHEN count(*) = 1
            AND max(outer_completed) = 2::UBIGINT
            AND max(child_calls) = 4::UBIGINT
            AND bool_and(done)
            AND bool_and(outer_aggregate_updated)
            AND bool_and(NOT outer_aggregate_can_stop)
            AND bool_and(NOT last_child_updated)
            AND bool_and(last_child_can_stop)
        THEN 'ok'
        ELSE error('nested Repeat/Saturate flag assertion failed')
    END AS status
FROM nested_controller;

-- Sequence advances through every child even when an earlier child's flags
-- could stop Repeat or Saturate.  Report aggregation remains OR(updated) and
-- AND(can_stop), while the ordered history proves all children executed.
WITH RECURSIVE sequence_controller(
    unit,
    next_child,
    history,
    aggregate_updated,
    aggregate_can_stop
) USING KEY (unit) AS (
    (VALUES (TRUE, 0::UBIGINT, []::UBIGINT[], FALSE, TRUE))
    UNION ALL
    (
        SELECT
            TRUE,
            next_child + 1,
            list_append(history, next_child),
            aggregate_updated OR next_child = 1,
            aggregate_can_stop AND next_child <> 1
        FROM sequence_controller
        WHERE next_child < 3
    )
)
SELECT
    'sequence_non_short_circuit_aggregation' AS test,
    CASE
        WHEN count(*) = 1
            AND max(next_child) = 3
            AND max(history) = [0::UBIGINT, 1::UBIGINT, 2::UBIGINT]
            AND bool_and(aggregate_updated)
            AND bool_and(NOT aggregate_can_stop)
        THEN 'ok'
        ELSE error('Sequence aggregation assertion failed')
    END AS status
FROM sequence_controller;

-- Same-wave, same-dependency sibling targets expose the sticky target-batch
-- rule directly.  Global event reselection would produce 1,2,3,4; latching H
-- after event 1 must instead drain H event 3 before selecting L events 2 and 4.
WITH RECURSIVE target_batch_latch(
    unit,
    queue,
    latch_wave,
    latch_target,
    history
) USING KEY (unit) AS (
    (
        VALUES (
            TRUE,
            [
                struct_pack(
                    ordinal := 1::UBIGINT,
                    wave := 0::UBIGINT,
                    rank := 0::UTINYINT,
                    target := 'H'
                ),
                struct_pack(
                    ordinal := 2::UBIGINT,
                    wave := 0::UBIGINT,
                    rank := 0::UTINYINT,
                    target := 'L'
                ),
                struct_pack(
                    ordinal := 3::UBIGINT,
                    wave := 0::UBIGINT,
                    rank := 0::UTINYINT,
                    target := 'H'
                ),
                struct_pack(
                    ordinal := 4::UBIGINT,
                    wave := 0::UBIGINT,
                    rank := 0::UTINYINT,
                    target := 'L'
                )
            ],
            0::UBIGINT,
            '',
            []::UBIGINT[]
        )
    )
    UNION ALL
    (
        SELECT
            TRUE,
            list_filter(
                working.queue,
                lambda queued: queued.ordinal <> event.ordinal
            ),
            event.wave,
            event.target,
            list_append(working.history, event.ordinal)
        FROM target_batch_latch AS working
        CROSS JOIN LATERAL (
            SELECT candidate.event
            FROM unnest(working.queue) AS candidate(event)
            WHERE NOT EXISTS (
                SELECT 1
                FROM unnest(working.queue) AS pending(event)
                WHERE pending.event.wave = working.latch_wave
                  AND pending.event.target = working.latch_target
            )
               OR (
                    candidate.event.wave = working.latch_wave
                    AND candidate.event.target = working.latch_target
               )
            ORDER BY candidate.event.wave, candidate.event.rank, candidate.event.ordinal
            LIMIT 1
        ) AS selected(event)
        WHERE len(working.queue) > 0
    )
)
SELECT
    'same_rank_target_batch_latch' AS test,
    CASE
        WHEN count(*) = 1
            AND max(len(queue)) = 0
            AND max(history) = [1::UBIGINT, 3::UBIGINT, 2::UBIGINT, 4::UBIGINT]
        THEN 'ok'
        ELSE error('same-rank target-batch latch assertion failed')
    END AS status
FROM target_batch_latch;

-- Current one-Fresh Packed_2 hot SCC.  Two View collisions generate Packed and
-- UF events.  The second UF event displaces its owner and generates the third
-- Packed row plus a wave-two UF event.  The selected target is latched until
-- its fixed (wave, target) batch drains, matching the committed runtime.
WITH RECURSIVE proof_kernel(unit, state) USING KEY (unit) AS (
    (
        SELECT
            TRUE,
            struct_pack(
                steps := 0::UBIGINT,
                next_fresh := 100::UBIGINT,
                next_event := 2::UBIGINT,
                latch_wave := 0::UBIGINT,
                latch_target := '',
                queue := [
                    struct_pack(
                        ordinal := 1::UBIGINT,
                        wave := 0::UBIGINT,
                        rank := 0::UTINYINT,
                        target := 'View',
                        key := 1::UBIGINT,
                        arg0 := 10::UBIGINT,
                        arg1 := 41::UBIGINT,
                        spelling := ''
                    ),
                    struct_pack(
                        ordinal := 2::UBIGINT,
                        wave := 0::UBIGINT,
                        rank := 0::UTINYINT,
                        target := 'View',
                        key := 2::UBIGINT,
                        arg0 := 15::UBIGINT,
                        arg1 := 42::UBIGINT,
                        spelling := ''
                    )
                ],
                packed := []::STRUCT(
                    id UBIGINT,
                    spelling VARCHAR,
                    hi_proof UBIGINT,
                    lo_proof UBIGINT
                )[],
                views := [
                    struct_pack(key := 1::UBIGINT, parent := 20::UBIGINT, proof := 40::UBIGINT),
                    struct_pack(key := 2::UBIGINT, parent := 20::UBIGINT, proof := 43::UBIGINT)
                ],
                ufs := []::STRUCT(key UBIGINT, parent UBIGINT, proof UBIGINT)[],
                history := []::UBIGINT[]
            )
    )
    UNION ALL
    (
        SELECT
            TRUE,
            struct_update(
                working.state,
                steps := working.state.steps + 1,
                next_fresh := working.state.next_fresh
                    + CASE WHEN decision.collision THEN 1 ELSE 0 END,
                next_event := working.state.next_event
                    + CASE WHEN decision.collision THEN 2 ELSE 0 END,
                latch_wave := event.wave,
                latch_target := event.target,
                queue := list_concat(
                    list_filter(
                        working.state.queue,
                        lambda queued: queued.ordinal <> event.ordinal
                    ),
                    CASE
                        WHEN decision.collision THEN [
                            struct_pack(
                                ordinal := working.state.next_event + 1,
                                wave := event.wave + 1,
                                rank := 1::UTINYINT,
                                target := 'Packed_2',
                                key := working.state.next_fresh,
                                arg0 := decision.hi_proof,
                                arg1 := decision.lo_proof,
                                spelling := CASE
                                    WHEN event.target = 'View' THEN 'trans_p0_sym_p1'
                                    ELSE 'trans_sym_p0_p1'
                                END
                            ),
                            struct_pack(
                                ordinal := working.state.next_event + 2,
                                wave := event.wave + 1,
                                rank := 1::UTINYINT,
                                target := 'UF',
                                key := decision.displaced_parent,
                                arg0 := decision.keep_parent,
                                arg1 := working.state.next_fresh,
                                spelling := ''
                            )
                        ]
                        ELSE []::STRUCT(
                            ordinal UBIGINT,
                            wave UBIGINT,
                            rank UTINYINT,
                            target VARCHAR,
                            key UBIGINT,
                            arg0 UBIGINT,
                            arg1 UBIGINT,
                            spelling VARCHAR
                        )[]
                    END
                ),
                packed := CASE
                    WHEN event.target = 'Packed_2' THEN list_append(
                        working.state.packed,
                        struct_pack(
                            id := event.key,
                            spelling := event.spelling,
                            hi_proof := event.arg0,
                            lo_proof := event.arg1
                        )
                    )
                    ELSE working.state.packed
                END,
                views := CASE
                    WHEN event.target = 'View' THEN list_append(
                        list_filter(working.state.views, lambda row: row.key <> event.key),
                        struct_pack(
                            key := event.key,
                            parent := decision.keep_parent,
                            proof := decision.keep_proof
                        )
                    )
                    ELSE working.state.views
                END,
                ufs := CASE
                    WHEN event.target = 'UF' THEN list_append(
                        list_filter(working.state.ufs, lambda row: row.key <> event.key),
                        struct_pack(
                            key := event.key,
                            parent := decision.keep_parent,
                            proof := decision.keep_proof
                        )
                    )
                    ELSE working.state.ufs
                END,
                history := list_append(working.state.history, event.ordinal)
            )
        FROM proof_kernel AS working
        CROSS JOIN LATERAL (
            SELECT candidate.event
            FROM unnest(working.state.queue) AS candidate(event)
            WHERE NOT EXISTS (
                SELECT 1
                FROM unnest(working.state.queue) AS pending(event)
                WHERE pending.event.wave = working.state.latch_wave
                  AND pending.event.target = working.state.latch_target
            )
               OR (
                    candidate.event.wave = working.state.latch_wave
                    AND candidate.event.target = working.state.latch_target
               )
            ORDER BY candidate.event.wave, candidate.event.rank, candidate.event.ordinal
            LIMIT 1
        ) AS selected(event)
        CROSS JOIN LATERAL (
            SELECT CASE event.target
                WHEN 'View' THEN len(list_filter(
                    working.state.views,
                    lambda row: row.key = event.key
                ))
                WHEN 'UF' THEN len(list_filter(
                    working.state.ufs,
                    lambda row: row.key = event.key
                ))
                WHEN 'Packed_2' THEN len(list_filter(
                    working.state.packed,
                    lambda row: row.id = event.key
                ))
                ELSE error('unknown proof-kernel target')::UBIGINT
            END AS owner_count
        ) AS owner_presence
        CROSS JOIN LATERAL (
            SELECT
                CASE
                    WHEN owner_count > 1 THEN error('duplicate proof-kernel owner')::UBIGINT
                    WHEN owner_count = 0 THEN event.arg0
                    WHEN event.target = 'View' THEN list_extract(
                        list_filter(working.state.views, lambda row: row.key = event.key),
                        1
                    ).parent
                    WHEN event.target = 'UF' THEN list_extract(
                        list_filter(working.state.ufs, lambda row: row.key = event.key),
                        1
                    ).parent
                    ELSE event.arg0
                END AS old_parent,
                CASE
                    WHEN owner_count > 1 THEN error('duplicate proof-kernel owner')::UBIGINT
                    WHEN owner_count = 0 THEN event.arg1
                    WHEN event.target = 'View' THEN list_extract(
                        list_filter(working.state.views, lambda row: row.key = event.key),
                        1
                    ).proof
                    WHEN event.target = 'UF' THEN list_extract(
                        list_filter(working.state.ufs, lambda row: row.key = event.key),
                        1
                    ).proof
                    ELSE event.arg1
                END AS old_proof
        ) AS owner
        CROSS JOIN LATERAL (
            SELECT
                event.target IN ('View', 'UF')
                    AND owner_presence.owner_count = 1
                    AND owner.old_parent <> event.arg0 AS collision,
                least(owner.old_parent, event.arg0) AS keep_parent,
                greatest(owner.old_parent, event.arg0) AS displaced_parent,
                CASE
                    WHEN owner.old_parent <= event.arg0 THEN owner.old_proof
                    ELSE event.arg1
                END AS keep_proof,
                CASE
                    WHEN owner.old_parent >= event.arg0 THEN owner.old_proof
                    ELSE event.arg1
                END AS hi_proof,
                CASE
                    WHEN owner.old_parent <= event.arg0 THEN owner.old_proof
                    ELSE event.arg1
                END AS lo_proof
        ) AS decision
        WHERE len(working.state.queue) > 0
    )
)
SELECT
    'one_fresh_packed2_hot_scc' AS test,
    CASE
        WHEN state.steps = 8
            AND state.next_fresh = 103
            AND state.next_event = 8
            AND len(state.queue) = 0
            AND state.history = [
                1::UBIGINT,
                2::UBIGINT,
                3::UBIGINT,
                5::UBIGINT,
                4::UBIGINT,
                6::UBIGINT,
                7::UBIGINT,
                8::UBIGINT
            ]
            AND list_sort(state.history) = [
                1::UBIGINT,
                2::UBIGINT,
                3::UBIGINT,
                4::UBIGINT,
                5::UBIGINT,
                6::UBIGINT,
                7::UBIGINT,
                8::UBIGINT
            ]
            AND list_transform(state.packed, lambda row: row.id)
                = [100::UBIGINT, 101::UBIGINT, 102::UBIGINT]
            AND len(state.packed) = 3
            AND len(state.views) = 2
            AND len(state.ufs) = 2
            AND len(list_filter(
                state.packed,
                lambda row: row.id = 100
                    AND row.spelling = 'trans_p0_sym_p1'
                    AND row.hi_proof = 40
                    AND row.lo_proof = 41
            )) = 1
            AND len(list_filter(
                state.packed,
                lambda row: row.id = 101
                    AND row.spelling = 'trans_p0_sym_p1'
                    AND row.hi_proof = 43
                    AND row.lo_proof = 42
            )) = 1
            AND len(list_filter(
                state.packed,
                lambda row: row.id = 102
                    AND row.spelling = 'trans_sym_p0_p1'
                    AND row.hi_proof = 101
                    AND row.lo_proof = 100
            )) = 1
            AND len(list_filter(
                state.views,
                lambda row: row.key = 1 AND row.parent = 10 AND row.proof = 41
            )) = 1
            AND len(list_filter(
                state.views,
                lambda row: row.key = 2 AND row.parent = 15 AND row.proof = 42
            )) = 1
            AND len(list_filter(
                state.ufs,
                lambda row: row.key = 20 AND row.parent = 10 AND row.proof = 100
            )) = 1
            AND len(list_filter(
                state.ufs,
                lambda row: row.key = 15 AND row.parent = 10 AND row.proof = 102
            )) = 1
        THEN 'ok'
        ELSE error('one-Fresh Packed_2 hot SCC assertion failed')
    END AS status
FROM proof_kernel;

-- Fresh allocation, generation, watermark, and effects share one transaction.
-- Explicit rollback restores all four; retry then publishes them together.
CREATE TEMP TABLE kernel_metadata (
    next_fresh UBIGINT NOT NULL,
    generation UBIGINT NOT NULL,
    watermark UBIGINT NOT NULL
);
INSERT INTO kernel_metadata VALUES (100, 7, 11);
CREATE TEMP TABLE kernel_effects (
    source_ordinal UBIGINT PRIMARY KEY,
    proof UBIGINT NOT NULL
);

BEGIN TRANSACTION;
UPDATE kernel_metadata
SET next_fresh = next_fresh + 3,
    generation = generation + 1,
    watermark = watermark + 1;
INSERT INTO kernel_effects VALUES (1, 100), (2, 101), (3, 102);
ROLLBACK;

SELECT
    'transactional_metadata_rollback' AS test,
    CASE
        WHEN (SELECT count(*) FROM kernel_metadata) = 1
            AND (SELECT next_fresh FROM kernel_metadata) = 100
            AND (SELECT generation FROM kernel_metadata) = 7
            AND (SELECT watermark FROM kernel_metadata) = 11
            AND (SELECT count(*) FROM kernel_effects) = 0
        THEN 'ok'
        ELSE error('transactional metadata rollback assertion failed')
    END AS status;

BEGIN TRANSACTION;
UPDATE kernel_metadata
SET next_fresh = next_fresh + 3,
    generation = generation + 1,
    watermark = watermark + 1;
INSERT INTO kernel_effects VALUES (1, 100), (2, 101), (3, 102);
COMMIT;

SELECT
    'transactional_metadata_commit' AS test,
    CASE
        WHEN (SELECT next_fresh FROM kernel_metadata) = 103
            AND (SELECT generation FROM kernel_metadata) = 8
            AND (SELECT watermark FROM kernel_metadata) = 12
            AND (SELECT list(proof ORDER BY source_ordinal) FROM kernel_effects)
                = [100::UBIGINT, 101::UBIGINT, 102::UBIGINT]
        THEN 'ok'
        ELSE error('transactional metadata commit assertion failed')
    END AS status;

-- Arithmetic is admitted only with an explicit wider-domain bounds check.
-- The mixed rows require vector-masked CASE evaluation: the out-of-BIGINT row
-- is safe only because the guarded branch is not selected.  The harness also
-- selects the rejection branch and separately proves direct BIGINT overflow.
WITH arithmetic_inputs(id, lhs, rhs, select_checked, expected) AS (
    VALUES
        (0::UBIGINT, 7::HUGEINT, 5::HUGEINT, TRUE, 12::BIGINT),
        (
            1::UBIGINT,
            9223372036854775807::HUGEINT,
            1::HUGEINT,
            FALSE,
            99::BIGINT
        )
),
arithmetic_results AS (
    SELECT
        id,
        CASE
            WHEN select_checked THEN CASE
                WHEN lhs + rhs
                    BETWEEN '-9223372036854775808'::HUGEINT
                        AND '9223372036854775807'::HUGEINT
                THEN (lhs + rhs)::BIGINT
                ELSE error('checked addition overflow')::BIGINT
            END
            ELSE 99::BIGINT
        END AS result,
        expected
    FROM arithmetic_inputs
)
SELECT
    'checked_arithmetic_and_lazy_error' AS test,
    CASE
        WHEN (SELECT count(*) FROM arithmetic_results) = 2
            AND (
                SELECT bool_and(result IS NOT DISTINCT FROM expected)
                FROM arithmetic_results
            )
            AND CASE
                WHEN TRUE THEN 7::BIGINT
                ELSE 9223372036854775807::BIGINT + 1::BIGINT
            END = 7
            AND CASE
                WHEN FALSE THEN error('unreachable lazy error')::BIGINT
                ELSE 9::BIGINT
            END = 9
        THEN 'ok'
        ELSE error('checked arithmetic/lazy error assertion failed')
    END AS status;

-- Partial operations lower to a non-null dummy plus an explicit defined bit.
-- Raw DuckDB overflow/division behavior belongs to the harness probes and is
-- never admitted as an Egglog-shaped NULL value.
WITH partial_inputs(operation, lhs, rhs) AS (
    VALUES
        ('add', 9223372036854775807::HUGEINT, 1::HUGEINT),
        ('divide_zero', 1::HUGEINT, 0::HUGEINT),
        (
            'divide_overflow',
            '-9223372036854775808'::HUGEINT,
            '-1'::HUGEINT
        )
),
partial_results AS (
    SELECT
        operation,
        CASE
            WHEN operation = 'add' THEN CASE
                WHEN lhs + rhs
                    BETWEEN '-9223372036854775808'::HUGEINT
                        AND '9223372036854775807'::HUGEINT
                THEN (lhs + rhs)::BIGINT
                ELSE 0::BIGINT
            END
            ELSE (
                lhs // CASE
                    WHEN rhs <> 0
                      AND NOT (
                          lhs = '-9223372036854775808'::HUGEINT
                          AND rhs = '-1'::HUGEINT
                      )
                    THEN rhs
                    ELSE 1::HUGEINT
                END
            )::BIGINT
        END AS dummy_nonnull,
        CASE
            WHEN operation = 'add' THEN lhs + rhs
                BETWEEN '-9223372036854775808'::HUGEINT
                    AND '9223372036854775807'::HUGEINT
            ELSE rhs <> 0
                AND NOT (
                    lhs = '-9223372036854775808'::HUGEINT
                    AND rhs = '-1'::HUGEINT
                )
        END AS defined
    FROM partial_inputs
)
SELECT
    'partial_arithmetic_definedness' AS test,
    CASE
        WHEN count(*) = 3
            AND count(defined) = count(*)
            AND count(dummy_nonnull) = count(*)
            AND bool_and(NOT defined)
            AND count(*) FILTER (
                WHERE operation = 'add' AND dummy_nonnull = 0
            ) = 1
            AND count(*) FILTER (
                WHERE operation = 'divide_zero' AND dummy_nonnull = 1
            ) = 1
            AND count(*) FILTER (
                WHERE operation = 'divide_overflow'
                  AND dummy_nonnull = '-9223372036854775808'::BIGINT
            ) = 1
        THEN 'ok'
        ELSE error('partial arithmetic definedness assertion failed')
    END AS status
FROM partial_results;
