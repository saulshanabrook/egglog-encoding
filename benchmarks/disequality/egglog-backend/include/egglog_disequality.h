#ifndef EGGLOG_DISEQUALITY_H
#define EGGLOG_DISEQUALITY_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct EgglogDisequalityGraph EgglogDisequalityGraph;
typedef struct EgglogDisequalityTemplate EgglogDisequalityTemplate;
typedef struct EgglogCommandResult EgglogCommandResult;
typedef struct EgglogOwnedString EgglogOwnedString;

/* Graph handles and every clone derived from one are thread-confined because
 * they share execution and source-history state. Unfinished templates are also
 * thread-confined. A finished template may be read concurrently only through
 * egglog_disequality_graph_new_from_template; do not mutate or free it during
 * those calls. Independent handles may be used on separate threads. */

enum EgglogDisequalityEncoding {
  EGGLOG_DISEQUALITY_EE = 0,
  EGGLOG_DISEQUALITY_OEE = 1,
  EGGLOG_DISEQUALITY_NEE = 2,
  EGGLOG_DISEQUALITY_DE = 3,
};

enum EgglogCommandStatus {
  EGGLOG_COMMAND_SUCCESS = 0,
  EGGLOG_COMMAND_CHECK_FAILED = 1,
  EGGLOG_COMMAND_EXPECT_FAIL_FAILED = 2,
  EGGLOG_COMMAND_ERROR = 3,
};

enum EgglogCommandOutputKind {
  EGGLOG_OUTPUT_PRINT_FUNCTION_SIZE = 0,
  EGGLOG_OUTPUT_PRINT_ALL_FUNCTIONS_SIZE = 1,
  EGGLOG_OUTPUT_EXTRACT_BEST = 2,
  EGGLOG_OUTPUT_EXTRACT_VARIANTS = 3,
  EGGLOG_OUTPUT_PROVE_EXISTS = 4,
  EGGLOG_OUTPUT_OVERALL_STATISTICS = 5,
  EGGLOG_OUTPUT_PRINT_FUNCTION = 6,
  EGGLOG_OUTPUT_RUN_SCHEDULE = 7,
  EGGLOG_OUTPUT_USER_DEFINED = 8,
};

enum EgglogTermLanguage {
  EGGLOG_TERM_LANGUAGE_VEC = 0,
  EGGLOG_TERM_LANGUAGE_DIRECT = 1,
};

EgglogDisequalityTemplate *egglog_disequality_template_new(
    uint32_t encoding, uint32_t term_language, const char *sort_name);
uint32_t egglog_disequality_template_register_operator(
    EgglogDisequalityTemplate *template_, const char *source_name,
    const char *preferred_name, size_t arity);
int32_t egglog_disequality_template_finish(
    EgglogDisequalityTemplate *template_);
/* Set record_interactions to nonzero only when executable trace export is
 * required. Recording is disabled in normal benchmark runs. */
EgglogDisequalityGraph *egglog_disequality_graph_new_from_template(
    const EgglogDisequalityTemplate *template_, int32_t record_interactions);
void egglog_disequality_template_free(EgglogDisequalityTemplate *template_);
const char *egglog_disequality_template_last_error(
    const EgglogDisequalityTemplate *template_);

/* Set record_interactions to nonzero only when executable trace export is
 * required. */
EgglogDisequalityGraph *egglog_disequality_graph_new(
    uint32_t encoding, int32_t record_interactions);
EgglogDisequalityGraph *egglog_disequality_graph_clone(
    const EgglogDisequalityGraph *graph);
void egglog_disequality_graph_free(EgglogDisequalityGraph *graph);

uint64_t egglog_disequality_add(EgglogDisequalityGraph *graph,
                                const char *operator_name,
                                const uint64_t *children,
                                size_t child_count);
uint64_t egglog_disequality_add_atom(EgglogDisequalityGraph *graph,
                                     const char *atom_name);
uint64_t egglog_disequality_add_registered(EgglogDisequalityGraph *graph,
                                           uint32_t operator_id,
                                           const uint64_t *children,
                                           size_t child_count);
int32_t egglog_disequality_union(EgglogDisequalityGraph *graph, uint64_t lhs,
                                 uint64_t rhs);
int32_t egglog_disequality_disunion(EgglogDisequalityGraph *graph,
                                    uint64_t lhs, uint64_t rhs);
EgglogCommandResult *egglog_disequality_flush(EgglogDisequalityGraph *graph);
EgglogCommandResult *egglog_disequality_rebuild(EgglogDisequalityGraph *graph);
EgglogCommandResult *egglog_disequality_check_equal(
    EgglogDisequalityGraph *graph, uint64_t lhs, uint64_t rhs);
EgglogCommandResult *egglog_disequality_check_known_disequal(
    EgglogDisequalityGraph *graph, uint64_t lhs, uint64_t rhs);
/* This executes the egglog command `(fail (check-disequalities))`.
 * SUCCESS means a contradiction was observed; EXPECT_FAIL_FAILED means the
 * graph was consistent. */
EgglogCommandResult *egglog_disequality_check_consistency(
    EgglogDisequalityGraph *graph);

/* Every command function returns an owned non-null result, including backend
 * errors. The caller must release it with egglog_command_result_free. Text
 * pointers remain valid until that result is freed. */
int32_t egglog_command_result_status(const EgglogCommandResult *result);
size_t egglog_command_result_output_count(const EgglogCommandResult *result);
int32_t egglog_command_result_output_kind(const EgglogCommandResult *result,
                                          size_t index);
const char *egglog_command_result_output_text(
    const EgglogCommandResult *result, size_t index);
const char *egglog_command_result_error(const EgglogCommandResult *result);
void egglog_command_result_free(EgglogCommandResult *result);

uint64_t egglog_disequality_num_nodes(EgglogDisequalityGraph *graph);
uint64_t egglog_disequality_num_classes(EgglogDisequalityGraph *graph);
uint64_t egglog_disequality_num_extension_rows(EgglogDisequalityGraph *graph);
uint64_t egglog_disequality_num_tuples(EgglogDisequalityGraph *graph);

/* Source export fails unless record_interactions was enabled at creation.
 * The caller owns a non-null result and must free it with
 * egglog_owned_string_free. */
EgglogOwnedString *egglog_disequality_source(EgglogDisequalityGraph *graph);
EgglogOwnedString *egglog_disequality_desugared_source(
    EgglogDisequalityGraph *graph);
const char *egglog_owned_string_data(const EgglogOwnedString *value);
size_t egglog_owned_string_len(const EgglogOwnedString *value);
void egglog_owned_string_free(EgglogOwnedString *value);
const char *egglog_disequality_last_error(
    const EgglogDisequalityGraph *graph);

#ifdef __cplusplus
}
#endif

#endif
