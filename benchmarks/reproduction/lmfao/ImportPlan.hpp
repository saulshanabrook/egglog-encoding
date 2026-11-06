// Adapter for the pinned covariance workload. This performs no optimization.
#include <boost/property_tree/json_parser.hpp>
#include <cstdlib>
#include <functional>
#include <stdexcept>

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
