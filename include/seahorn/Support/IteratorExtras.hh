#pragma once
/** Utility functions for iterators */

#include <boost/iterator/zip_iterator.hpp>
#include <boost/range.hpp>

namespace seahorn {
using namespace boost;

template <typename Iterator1, typename Iterator2>
boost::zip_iterator<boost::tuple<Iterator1, Iterator2>>
mk_zip_it(Iterator1 it1, Iterator2 it2) {
  return make_zip_iterator(make_tuple(it1, it2));
}

template <typename Range1, typename Range2,
          typename Iterator1 = typename boost::range_iterator<Range1>::type,
          typename Iterator2 = typename boost::range_iterator<Range2>::type>
boost::iterator_range<boost::zip_iterator<boost::tuple<Iterator1, Iterator2>>>
mk_zip_rng(Range1 &r1, Range2 &r2) {
  return make_iterator_range(mk_zip_it(boost::begin(r1), boost::begin(r2)),
                             mk_zip_it(boost::end(r1), boost::end(r2)));
}

} // namespace ufo
