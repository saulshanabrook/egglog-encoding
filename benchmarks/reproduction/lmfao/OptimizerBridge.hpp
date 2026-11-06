// JSON boundary for the pinned covariance frontend and logical optimizer.
#include "ImportPlan.hpp"
#include <cerrno>
#include <fstream>
#include <sys/wait.h>
#include <unistd.h>

namespace lmfao_bridge {
using boost::property_tree::ptree;

template<class T> static ptree scalar(const T& value) {
    ptree result;
    result.put_value(value);
    return result;
}
template<size_t N> static ptree indices(const std::bitset<N>& bits) {
    ptree result;
    for (size_t i = 0; i < N; ++i)
        if (bits.test(i)) result.push_back({"", scalar(i)});
    return result;
}
static void require(bool ok) {
    if (!ok) throw std::runtime_error("Unsupported LMFAO optimizer bridge input");
}
static ptree aggregate(const Aggregate* agg) {
    require(agg->_agg.size() == 1);
    ptree result, incoming;
    result.add_child("functions", indices(agg->_agg[0]));
    for (const auto& edge : agg->_incoming) {
        ptree pair;
        pair.push_back({"", scalar(edge.first)});
        pair.push_back({"", scalar(edge.second)});
        incoming.push_back({"", pair});
    }
    result.add_child("incoming", incoming);
    return result;
}
static void exportWorkload(const char* path, std::shared_ptr<TreeDecomposition> td,
                           const std::vector<Query*>& queries,
                           const std::vector<Function*>& functions) {
    ptree result, attributes, relations, fs, qs;
    result.put("root", td->_root->_id);
    for (size_t i = 0; i < td->numberOfAttributes(); ++i) {
        const auto* a = td->getAttribute(i);
        require(a->_type == Integer || a->_type == Double);
        ptree value;
        value.put("name", a->_name);
        value.put("type", a->_type == Double ? "double" : "int");
        attributes.push_back({"", value});
    }
    for (size_t i = 0; i < td->numberOfRelations(); ++i) {
        const auto* r = td->getRelation(i);
        ptree value, neighbors;
        value.put("name", r->_name);
        value.add_child("attributes", indices(r->_bag));
        for (size_t n : r->_neighbors) neighbors.push_back({"", scalar(n)});
        value.add_child("neighbors", neighbors);
        relations.push_back({"", value});
    }
    for (const Function* f : functions) {
        require(f->_fVars.count() == 1 && !f->_dynamic && f->_parameter == nullptr);
        require(f->_operation == sum || f->_operation == quadratic_sum);
        ptree value;
        value.add_child("attributes", indices(f->_fVars));
        value.put("power", f->_operation == sum ? 1 : 2);
        fs.push_back({"", value});
    }
    for (const Query* q : queries) {
        require(q->_aggregates.size() == 1);
        ptree value = aggregate(q->_aggregates[0]);
        value.erase("incoming");
        value.put("root", q->_rootID);
        value.add_child("keys", indices(q->_fVars));
        qs.push_back({"", value});
    }
    result.add_child("attributes", attributes);
    result.add_child("relations", relations);
    result.add_child("functions", fs);
    result.add_child("queries", qs);
    boost::property_tree::write_json(path, result);
}
static void exportPlan(const char* path, const std::vector<Query*>& queries,
                       const std::vector<View*>& views) {
    ptree result, vs, outputs;
    for (const View* v : views) {
        ptree value, aggregates;
        value.put("origin", v->_origin);
        value.put("destination", v->_destination);
        value.add_child("keys", indices(v->_fVars));
        for (const Aggregate* a : v->_aggregates) aggregates.push_back({"", aggregate(a)});
        value.add_child("aggregates", aggregates);
        vs.push_back({"", value});
    }
    for (const Query* q : queries) {
        require(q->_aggregates.size() == 1 && q->_aggregates[0]->_incoming.size() == 1);
        const auto edge = q->_aggregates[0]->_incoming[0];
        ptree value;
        value.put("view", edge.first);
        value.put("aggregate", edge.second);
        value.put("root", q->_rootID);
        outputs.push_back({"", value});
    }
    result.add_child("views", vs);
    result.add_child("outputs", outputs);
    boost::property_tree::write_json(path, result);
}
static void optimize(const char* config, const char* input, const char* output) {
    require(input && output);
    ptree settings;
    boost::property_tree::read_json(config, settings);
    std::vector<std::string> command;
    for (const auto& arg : settings.get_child("command")) command.push_back(arg.second.get_value<std::string>());
    require(!command.empty());
    command.push_back(config);
    command.push_back(input);
    command.push_back(output);
    std::vector<char*> argv;
    for (auto& arg : command) argv.push_back(&arg[0]);
    argv.push_back(nullptr);
    const pid_t child = fork();
    if (child == -1) throw std::runtime_error("Cannot start LMFAO optimizer");
    if (child == 0) {
        execvp(argv[0], argv.data());
        _exit(127);
    }
    int status;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited == -1 && errno == EINTR);
    if (waited != child || !WIFEXITED(status) || WEXITSTATUS(status) != 0)
        throw std::runtime_error("LMFAO optimizer subprocess failed");
}
} // namespace lmfao_bridge
