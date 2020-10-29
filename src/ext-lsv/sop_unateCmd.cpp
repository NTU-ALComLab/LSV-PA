#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <map>
#include <iostream>
using namespace std;

static int Lsv_CommandPrint_sop_unate(Abc_Frame_t *pAbc, int argc, char **argv);

void init_sop(Abc_Frame_t *pAbc)
{
	Cmd_CommandAdd(pAbc, "LSV_sopunate", "lsv_print_sopunate", Lsv_CommandPrint_sop_unate, 0);
}

void destroy_sop(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t sop_frame_initializer = {init_sop, destroy_sop};

struct PackageRegistrationManager
{
	PackageRegistrationManager() { Abc_FrameAddInitializer(&sop_frame_initializer); }
} lsv_sop_unate_PackageRegistrationManager;

void Lsv_NtkPrint_sop_uante(Abc_Ntk_t *pNtk)
{
	Abc_Obj_t *pObj;
	int i;
	if (Abc_NtkHasSop(pNtk))
	{
		Abc_NtkForEachNode(pNtk, pObj, i)
		{
			// printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));

			Abc_Obj_t *pFanin;
			int j;
			int fanin_num = Abc_ObjFaninNum(pObj);
			if(fanin_num != 0)
				printf("node %s:\n", Abc_ObjName(pObj));
			int single_sop_len = fanin_num + 3; //(a space add 1 or 0 add \n)
			// int
			// bool pos_u [fanin_num];
			// bool neg_u [fanin_num];
			vector<bool> pos_u, neg_u, bin_u;
			pos_u.resize(fanin_num, true);
			neg_u.resize(fanin_num, true);
			bin_u.resize(fanin_num, true);
			vector<Abc_Obj_t *> fanin_arr ;
			map<int,string> fanin_map;
			map<int,string>::iterator fanin_it;
			map<int,int> fanin_id_2_order;
			// fanin_arr.reserve(fanin_num);
			Abc_ObjForEachFanin(pObj, pFanin, j)
			{
				// printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
				// fanin_arr.push_back(pFanin);
				fanin_map[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
				fanin_id_2_order[Abc_ObjId(pFanin)] = j;
			}
			string Sop_str = (char *)pObj->pData;
			// cout << Sop_str << endl;
			// cout << Sop_str.size() << endl;
			int Sop_num = Sop_str.size() / single_sop_len;
			int addr = 0;
			bool offset_sop = false;
			for (int k = 0; k < Sop_num; k++)
			{
				for (int l = 0; l < fanin_num ; l++)
				{
					if (Sop_str[addr] == '1')
					{
						// cout << "get one";
						// pos_u[l] = true;
						neg_u[l] = false;
					}
					else if(Sop_str[addr] == '0'){
						// cout << "get zero";
						pos_u[l] = false;
					}
					addr += 1;
				}
				addr += 1;
				// cout<<Sop_str[addr]<<endl;
				if(Sop_str[addr] == '0'){
					// cout<<"why"<<endl;
					offset_sop = true;
				}
				addr += 2;
			}

			//binate processing
			for(int l = 0; l < fanin_num; l++){
				bin_u[l] = ( !pos_u[l] && !neg_u[l] ); 
			}
			// cout<<"offset is: "<<offset_sop<<endl;
			if(offset_sop){
				vector<bool> tmp = neg_u;
				neg_u = pos_u;
				pos_u = tmp;
			}
			// +unate inputs: c,d
			string pos_str, neg_str, bin_str;
			j = 0;
			for(fanin_it = fanin_map.begin(); fanin_it != fanin_map.end(); fanin_it++, j++)
			{
				// printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
				int order = fanin_id_2_order[fanin_it->first];
				if(pos_u[order]){
					pos_str += fanin_it->second;
					pos_str += ",";
					// cout<<pos_str<<endl;
				}
				if(neg_u[order]){
					neg_str += fanin_it->second;
					neg_str += ",";
				}
				if(bin_u[order]){
					bin_str += fanin_it->second;
					bin_str += ",";
				}
			}
			if(pos_str.size() != 0){
				pos_str.resize (pos_str.size () - 1);
				cout<<"+unate inputs: ";
				cout<<pos_str<<endl;
			}
			if(neg_str.size() != 0){
				// neg_str.pop_back();
				neg_str.resize (neg_str.size () - 1);				
				cout<<"-unate inputs: ";
				cout<<neg_str<<endl;
			}
			if(bin_str.size() != 0){
				// bin_str.pop_back();
				bin_str.resize (bin_str.size () - 1);				
				cout<<"binate inputs: ";
				cout<<bin_str<<endl;
			}

			// cout<<"postive unate: "<<endl;
			// for(int l = 0; l < fanin_num; l++){
			// 	cout<<pos_u[l]<<" "<<endl;
			// }
			
			// cout<<"negative unate: "<<endl;
			// for(int l = 0; l < fanin_num; l++){
			// 	cout<<neg_u[l]<<" "<<endl;
			// }

			// cout<<"binate: "<<endl;
			// for(int l = 0; l < fanin_num; l++){
			// 	cout<<bin_u[l]<<" "<<endl;
			// }
			// if (Abc_NtkHasSop(pNtk)) {
			//   printf("The SOP of this node:\n%s", (char*)pObj->pData);
			// }
		}
	}
}

int Lsv_CommandPrint_sop_unate(Abc_Frame_t *pAbc, int argc, char **argv)
{
	Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
	int c;
	Extra_UtilGetoptReset();
	while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
	{
		switch (c)
		{
		case 'h':
			goto usage;
		default:
			goto usage;
		}
	}
	if (!pNtk)
	{
		Abc_Print(-1, "Empty network.\n");
		return 1;
	}
	Lsv_NtkPrint_sop_uante(pNtk);
	return 0;

usage:
	Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
	Abc_Print(-2, "\t        prints the sopunate in the network\n");
	Abc_Print(-2, "\t-h    : print the command usage\n");
	return 1;
}