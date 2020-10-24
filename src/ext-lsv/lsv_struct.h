#ifndef LSV_STRUCT_H
#define LSV_STRUCT_H

#include <iostream>

namespace lsv
{

enum Unateness { NONE, POS_UNATE, NEG_UNATE, BINATE };
Unateness operator!(const Unateness& rhs);
Unateness operator+(const Unateness& lhs, const Unateness& rhs);
Unateness& operator+=(Unateness& lhs, const Unateness& rhs);
std::ostream& operator<<(std::ostream& os, const Unateness& rhs);

}   /// end of namespace lsv

#endif