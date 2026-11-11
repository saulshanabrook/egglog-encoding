// JSON boundary for the pinned covariance frontend and logical optimizer.
#include <boost/property_tree/json_parser.hpp>
#include <cstdlib>
#include <functional>
#include <stdexcept>
#include <boost/rational.hpp>

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
// Paper section 3.3, on the supplied join tree. The pinned Favorita workload
// has a strict winner for every query, so its size-based tie break is unused.
static void coverageRoots(std::shared_ptr<TreeDecomposition> td,
                          const std::vector<Query*>& queries) {
    using Weight = boost::rational<size_t>;
    const size_t count = td->numberOfRelations();
    std::vector<Weight> weights(count, Weight(0));
    for (const Query* q : queries) {
        for (size_t i = 0; i < count; ++i) {
            const size_t overlap = (q->_fVars & td->getRelation(i)->_bag).count();
            weights[i] += q->_fVars.none() ? Weight(1, count) : Weight(overlap, q->_fVars.count());
        }
    }
    for (Query* q : queries) {
        size_t best = count;
        bool tied = false;
        for (size_t i = 0; i < count; ++i) {
            if (q->_fVars.any() && (q->_fVars & td->getRelation(i)->_bag).none()) continue;
            if (best == count || weights[i] > weights[best]) {
                best = i;
                tied = false;
            } else if (weights[i] == weights[best]) {
                tied = true;
            }
        }
        require(best != count && !tied);
        q->_rootID = best;
    }
    std::cerr << "LMFAO paper coverage roots: " << queries.size() << " queries\n";
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
static void importPlan(const char* filename, std::shared_ptr<TreeDecomposition> td,
                       std::vector<Query*>& queries, std::vector<View*>& views,
                       const std::vector<Function*>& functions)
{
    using boost::property_tree::ptree;
    ptree plan;
    boost::property_tree::read_json(filename, plan);
    auto require = [](bool ok) { if (!ok) throw std::runtime_error("Invalid extracted LMFAO plan"); };
    require(views.empty());
    for (const auto& entry : plan.get_child("views")) {
        const auto& value = entry.second;
        auto origin = value.get<unsigned>("origin");
        auto destination = value.get<unsigned>("destination");
        require(origin < td->numberOfRelations() && destination < td->numberOfRelations());
        View* view = new View(origin, destination);
        view->_usageCount = view->_numberIncomingViews = 0;
        for (const auto& key : value.get_child("keys"))
            view->_fVars.set(key.second.get_value<size_t>());
        for (const auto& item : value.get_child("aggregates")) {
            Aggregate* aggregate = new Aggregate();
            prod_bitset product;
            for (const auto& function : item.second.get_child("functions")) {
                size_t id = function.second.get_value<size_t>();
                require(id < functions.size());
                product.set(id);
            }
            aggregate->_agg.push_back(product);
            for (const auto& edge : item.second.get_child("incoming")) {
                require(edge.second.size() == 2);
                auto it = edge.second.begin();
                size_t v = (it++)->second.get_value<size_t>();
                size_t a = it->second.get_value<size_t>();
                aggregate->_incoming.emplace_back(v, a);
            }
            view->_aggregates.push_back(aggregate);
        }
        require(!view->_aggregates.empty());
        views.push_back(view);
    }
    std::vector<unsigned> state(views.size(), 0);
    std::function<void(size_t)> visit = [&](size_t i) {
        require(i < views.size() && state[i] != 1);
        if (state[i] == 2) return;
        state[i] = 1;
        View* view = views[i];
        TDNode* node = td->getRelation(view->_origin);
        std::vector<size_t> neighbors;
        bool legal = view->_origin == view->_destination;
        for (size_t j = 0; j < node->_numOfNeighbors; ++j) {
            size_t id = node->_neighbors[j];
            if (id == view->_destination) legal = true;
            else neighbors.push_back(id);
        }
        require(legal);
        for (Aggregate* aggregate : view->_aggregates) {
            require(aggregate->_incoming.size() == neighbors.size());
            for (size_t j = 0; j < neighbors.size(); ++j) {
                const auto edge = aggregate->_incoming[j];
                require(edge.first < views.size());
                View* child = views[edge.first];
                require(child->_origin == neighbors[j] && child->_destination == view->_origin);
                require(edge.second < child->_aggregates.size());
                visit(edge.first);
            }
        }
        state[i] = 2;
    };
    for (size_t i = 0; i < views.size(); ++i) visit(i);
    const auto& outputs = plan.get_child("outputs");
    require(outputs.size() == queries.size());
    size_t i = 0;
    for (const auto& output : outputs) {
        Query* query = queries[i++];
        size_t v = output.second.get<size_t>("view");
        size_t a = output.second.get<size_t>("aggregate");
        require(v < views.size() && a < views[v]->_aggregates.size());
        require(query->_aggregates.size() == 1 && query->_fVars == views[v]->_fVars);
        require(views[v]->_origin == views[v]->_destination);
        query->_rootID = views[v]->_origin;
        query->_aggregates[0]->_incoming.emplace_back(v, a);
    }
    std::cerr << "LMFAO imported selected DAG: " << views.size() << " views\n";
}

} // namespace lmfao_bridge
