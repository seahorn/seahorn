#pragma once
/**
   Extra utilities for boost::property_map interface
 */

namespace seahorn {
template <typename Set> struct SetPropertyMap {
  typedef bool value_type;
  typedef bool reference;
  typedef typename Set::key_type key_type;
  typedef read_write_property_map_tag category;

  typedef SetPropertyMap<Set> this_type;

  Set *set;
  SetPropertyMap() : set(NULL) {}
  SetPropertyMap(Set &s) : set(&s) {}
  SetPropertyMap(const this_type &other) : set(other.set) {}

  this_type &operator=(const this_type &other) {
    this_type tmp(other);
    set = other.set;
    return *this;
  }
};

template <typename Set> SetPropertyMap<Set> make_set_property_map(Set &s) {
  return SetPropertyMap<Set>(s);
}
} // namespace ufo

namespace boost {
template <typename Set>
bool get(const ufo::SetPropertyMap<Set> &pm, typename Set::key_type key) {
  assert(pm.set != NULL);
  return pm.set->count(key) > 0;
}

template <typename Set>
void put(ufo::SetPropertyMap<Set> &pm, typename Set::key_type key, bool val) {
  assert(pm.set != NULL);
  if (val)
    pm.set->insert(key);
  else
    pm.set->erase(key);
}
} // namespace boost

