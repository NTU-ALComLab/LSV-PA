
#include "ext-lsv/lsv_struct.h"

namespace lsv
{

Unateness operator!(const Unateness& rhs)
{
    if( rhs==POS_UNATE ) return NEG_UNATE;
    if( rhs==NEG_UNATE ) return POS_UNATE;
    return rhs; 
}

Unateness operator+(const Unateness& lhs, const Unateness& rhs)
{
    return (Unateness)(lhs|rhs);
}

Unateness& operator+=(Unateness& lhs, const Unateness& rhs)
{
    return lhs = (Unateness)(lhs|rhs);
}

std::ostream& operator<<(std::ostream& os, const Unateness& rhs)
{
    switch( rhs )
    {
        case POS_UNATE :
            os << '1';
            break;
        case NEG_UNATE :
            os << '0';
            break;
        case BINATE :
            os << '-';
            break;
        default:
            os << 'x';
            break;
    }
    return os;
}

}   /// end of namespace lsv
