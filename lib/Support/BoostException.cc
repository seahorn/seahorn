#include <boost/version.hpp>
#include <cstdlib>
#include <exception>

#if BOOST_VERSION / 100 % 100 >= 73
#include <boost/assert/source_location.hpp>
#endif

#ifdef BOOST_NO_EXCEPTIONS
namespace boost {
void throw_exception(std::exception const &e) {
  // TBD: print error message
  std::exit(1);
}
#if BOOST_VERSION / 100 % 100 >= 73
// Starting with boost 1.73
void throw_exception(std::exception const &e,
                     boost::source_location const &loc) {
  // TBD: print error message
  std::exit(1);
}
#endif
} // namespace boost
#endif
