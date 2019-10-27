#pragma once
#include <boost/bimap.hpp>
#include <boost/bimap/list_of.hpp>
#include <boost/bimap/unordered_set_of.hpp>

namespace expr {
using namespace boost;

/** LRU Cache */
template <typename T> class ExprCache {
  using cache_type =
      boost::bimaps::bimap<boost::bimaps::unordered_set_of<ENode *>,
                           boost::bimaps::list_of<T>>;
  using value_type = typename cache_type::left_value_type;
  using right_iterator = typename cache_type::right_iterator;

  cache_type cache;
  size_t capacity;

public:
  using const_iterator = typename cache_type::left_const_iterator;
  using iterator = typename cache_type::left_iterator;

public:
  ExprCache(size_t c) : capacity(c) {}

  ~ExprCache() { clear(); }

  void clear() {
    for (auto it = cache.left.begin(), end = cache.left.end(); it != end;
         ++it) {
      ENode *n = it->first;
      n->efac().Deref(n);
    }
    cache.clear();
  }

  const_iterator find(Expr e) {
    auto it = cache.left.find(&*e);
    if (it != cache.left.end())
      cache.right.relocate(cache.right.end(), cache.project_right(it));
    return it;
  }

  const_iterator end() const { return cache.left.end(); }

  std::pair<iterator, bool> insert(Expr e, T &v) {
    if (cache.size() == capacity) {
      right_iterator it = cache.right.begin();
      // -- dereference a key that is about to be deleted
      ENode *old = it->second;
      old->efac().Deref(old);
      cache.right.erase(it);
    }
    ENode *n = &*e;
    n->Ref();
    return cache.left.insert(value_type(n, v));
  }

  size_t size() const { return cache.size(); }
};
} // namespace expr
