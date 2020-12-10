#include <string>
#include <algorithm>
using namespace std;

class FanIn{

    public:
        FanIn(int num, int id, string name){
            _num = num;
            _id = id;
            _name = name;
            _type = 0;
        }

        bool operator <(const FanIn &b) const{
            return _id < b._id;
        }

        bool operator >(const FanIn &b) const{
            return _id > b._id;
        }

        int _num;
        int _id;
        string _name;
        int _type;
        // 0: pos_unate and neg_unate
        // 1: pos_unate
        // 2: neg_unate
        // 3: binate

};



