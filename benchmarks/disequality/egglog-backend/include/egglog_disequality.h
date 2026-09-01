#ifndef EGGLOG_DISEQUALITY_H
#define EGGLOG_DISEQUALITY_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct EgglogDisequalityGraph EgglogDisequalityGraph;
typedef struct EgglogDisequalityTemplate EgglogDisequalityTemplate;

enum EgglogDisequalityEncoding {
  EGGLOG_DISEQUALITY_EE = 0,
  EGGLOG_DISEQUALITY_OEE = 1,
  EGGLOG_DISEQUALITY_NEE = 2,
  EGGLOG_DISEQUALITY_DE = 3,
};

enum EgglogDisequalityComparison {
  EGGLOG_COMPARISON_EQUAL = 0,
  EGGLOG_COMPARISON_UNEQUAL = 1,
  EGGLOG_COMPARISON_INDETERMINATE = 2,
  EGGLOG_COMPARISON_ERROR = -1,
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
int32_t egglog_disequality_rebuild(EgglogDisequalityGraph *graph);
int32_t egglog_disequality_compare(EgglogDisequalityGraph *graph,
                                   uint64_t lhs, uint64_t rhs);
int32_t egglog_disequality_is_consistent(EgglogDisequalityGraph *graph);

uint64_t egglog_disequality_num_nodes(EgglogDisequalityGraph *graph);
uint64_t egglog_disequality_num_classes(EgglogDisequalityGraph *graph);
uint64_t egglog_disequality_num_extension_rows(EgglogDisequalityGraph *graph);
uint64_t egglog_disequality_num_tuples(EgglogDisequalityGraph *graph);

/* Source export fails unless record_interactions was enabled at creation. */
int32_t egglog_disequality_write_source(EgglogDisequalityGraph *graph,
                                        const char *path);
int32_t egglog_disequality_write_desugared(EgglogDisequalityGraph *graph,
                                           const char *path);
int32_t egglog_disequality_write_snapshot(EgglogDisequalityGraph *graph,
                                          const char *source_path,
                                          const char *desugared_path);
const char *egglog_disequality_last_error(
    const EgglogDisequalityGraph *graph);

#ifdef __cplusplus
}
#endif

#endif
