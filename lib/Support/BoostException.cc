#include<cstdlib>
#include<exception>
#ifdef BOOST_NO_EXCEPTIONS
namespace boost {
void throw_exception(std::exception const &e) {
  // TBD: print error message
  std::exit(1);
}
} // namespace boost
#endif
