#pragma once

#define BOOST_DISABLE_ASSERTS 1
// boost/ptr_vector.hpp has BOOST_ASSERT that rely on rtti
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wsuggest-override"
#include <boost/ptr_container/ptr_vector.hpp>
#pragma clang diagnostic pop
#undef BOOST_DISABLE_ASSERTS
