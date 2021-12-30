#include <iostream>
#include <geas/mtl/int-triemap.h>

using std::cout;
using std::endl;

typedef triemap<char> map_t;

void test_iter(void) {
  map_t map;
  map.insert(88, 'c');
  map.insert(994, 'd');
  map.insert(13, 'b');
  map.insert(100000, 'e');
  map.insert(6, 'a');
  
  triemap_iterator_buffer buf;
  
  {
    cout << "forward iterator." << std::endl;
  auto it = map.fwd_begin(buf);
  auto en = map.fwd_end(buf);

  for(; it != en; ++it)
    cout << (*it).key << " => " << (*it).value << endl;
  }

  {
    cout << "backward iterator." << std::endl;
    auto it = map.bwd_begin(buf);
    auto en = map.bwd_end(buf);
    for(; it != en; ++it)
      cout << (*it).key << " => " << (*it).value << endl;
  }
      
  {
    cout << "<after> iterator sequence." << std::endl;
    auto it = map.dir_iter_after<false>(buf, 13);
    auto en = map.fwd_end(buf);

    for(; it != en; ++it)
      cout << (*it).key << " => " << (*it).value << endl;
  }
  
  {
    cout << "<before> iterator sequence." << std::endl;
    auto it = map.dir_iter_after<true>(buf, 994);
    auto en = map.bwd_end(buf);

    for(; it != en; ++it)
      cout << (*it).key << " => " << (*it).value << endl;
  }

}

int main(int argc, char** argv) {
  test_iter();
}
