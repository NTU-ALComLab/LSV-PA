#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver2.h"
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
using namespace std;
extern "C" Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *, int, int);
// extern "C"

static int Lsv_CommandPrint_poUnate(Abc_Frame_t *pAbc, int argc, char **argv);

void init_pounate(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrint_poUnate, 0);
}

void destroy_pounate(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t pounate_frame_initializer = {init_pounate, destroy_pounate};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&pounate_frame_initializer); }
} lsv_pounate_PackageRegistrationManager;

void Lsv_NtkPrint_pounate_one_output(Abc_Ntk_t *pNtk, Abc_Ntk_t * oNtk, bool neg_output)
{
  Abc_Obj_t *pObj;
  Aig_Man_t *aig_obj;
  Cnf_Dat_t *cnf_pos_obj, *cnf_neg_obj;
  aig_obj = Abc_NtkToDar(pNtk, 0, 0);
  int o_npi = Abc_NtkPiNum(oNtk);
  int npi = Aig_ManCiNum(aig_obj);
  int npo = Aig_ManCoNum(aig_obj);
  cnf_pos_obj = Cnf_Derive(aig_obj, npo);
  cnf_neg_obj = Cnf_DataDup(cnf_pos_obj);
  int num_var_cnf;
  num_var_cnf = cnf_pos_obj->nVars;
  Cnf_DataLift(cnf_neg_obj, num_var_cnf);

  //pi in aig

  map<int, string> fanin_map;
  map<int, string>::iterator fanin_it;
  map<int, int> fanin_order_2_id;
  map<string, int> in_map_name2id;
  vector<string> fanout_map;
  // Abc_Obj_t *pFanin;
  int j;
  Abc_NtkForEachCi(oNtk, pObj, j)
  {
    fanin_map[Abc_ObjId(pObj)] = Abc_ObjName(pObj);
    in_map_name2id[Abc_ObjName(pObj)] = Abc_ObjId(pObj);
  }

  Abc_NtkForEachCi(pNtk, pObj, j)
  {
    int ori_id = in_map_name2id[Abc_ObjName(pObj)];
    fanin_order_2_id[j] = ori_id;
  }



  Abc_NtkForEachPo(pNtk, pObj, j)
  {
    char* s = Abc_ObjName(pObj);
    fanout_map.push_back(s);
  }
  //map pi from aig to cnf
  int pi_cnf[npi];
  for (int i = 0; i < npi; i++)
  {
    int idx = Aig_ManCi(aig_obj, i)->Id;
    pi_cnf[i] = (cnf_pos_obj->pVarNums)[idx];
  }
  //map po from aig to cnf
  int po_cnf[npo];
  for (int i = 0; i < npo; i++)
  {
    int idx = Aig_ManCo(aig_obj, i)->Id;
    po_cnf[i] = (cnf_pos_obj->pVarNums)[idx];
  }

  sat_solver *sat_init = (sat_solver *)Cnf_DataWriteIntoSolver(cnf_pos_obj, 1, 0);
  sat_solver_setnvars(sat_init, num_var_cnf * 3);
  for (int i = 0; i < cnf_neg_obj->nClauses; i++)
  {
    sat_solver_addclause(sat_init, cnf_neg_obj->pClauses[i], cnf_neg_obj->pClauses[i + 1]);
  }

  for (int pi_idx = 0; pi_idx < npi; pi_idx++)
  {
    int p_i = pi_cnf[pi_idx];
    int n_i = p_i + num_var_cnf;
    int en_idx = pi_idx + 2 * num_var_cnf + 1;
    int fcompl = 0;
    sat_solver_add_buffer_enable(sat_init, p_i, n_i, en_idx, fcompl);
  }
  sat_solver_solve(sat_init, NULL, NULL, 0,0,0,0);

  for (int po_idx = 0; po_idx < npo; po_idx++)
  {
    // printf("node %s:\n", fanout_map[po_idx].c_str());
    cout<<"node "<<fanout_map[po_idx]<<":"<<endl;
    vector<bool> pos_u, neg_u, bin_u;
    pos_u.resize(o_npi, true);
    neg_u.resize(o_npi, true);
    bin_u.resize(o_npi, true); 
    // negative unate checking
    for (int pi_idx = 0; pi_idx < npi; pi_idx++)
    {
      // sat_solver* sat_init;
      // sat_init = (sat_solver*)Cnf_DataWriteIntoSolver(cnf_pos_obj,1,0);
      // sat_init = (sat_solver*)Cnf_DataWriteIntoSolverInt(sat_init,cnf_neg_obj,1,0);
      // int pos_po [1], neg_po[1];
      // pos_po[0] = toLitCond(po_cnf[po_idx], 0);
      // neg_po[0] = toLitCond(po_cnf[po_idx] + num_var_cnf, 1);
      // sat_solver_addclause(sat_init,pos_po,pos_po+1);
      // sat_solver_addclause(sat_init,neg_po,neg_po+1);
      int assump_num = 2 + 2 + (npi - 1);
      int assump_arr[assump_num];
      int p_in = pi_cnf[pi_idx];
      int n_in = p_in + num_var_cnf;

      assump_arr[0] = toLitCond(po_cnf[po_idx], 0);
      assump_arr[1] = toLitCond(po_cnf[po_idx] + num_var_cnf, 1);
      assump_arr[2] = toLitCond(p_in, 0);
      assump_arr[3] = toLitCond(n_in, 1);
      int assump_idx = 4;
      for (int i = 0; i < npi; i++)
      {
        int en_idx = i + 2 * num_var_cnf + 1;
        if (i != pi_idx)
        {
          assump_arr[assump_idx] = toLitCond(en_idx, 0);
          assump_idx += 1;
        }
      }
      int sat_result = sat_solver_solve(sat_init, assump_arr, assump_arr + assump_num, 0, 0, 0, 0);
      if (sat_result == l_True)
      {
        int n_id = fanin_order_2_id[pi_idx] - 1;
        neg_u[n_id] = false;

      }
    }
    //positive checking
    for (int pi_idx = 0; pi_idx < npi; pi_idx++)
    {
      int assump_num = 2 + 2 + (npi - 1);
      int assump_arr[assump_num];
      int p_in = pi_cnf[pi_idx];
      int n_in = p_in + num_var_cnf;
      assump_arr[0] = toLitCond(po_cnf[po_idx], 1);
      assump_arr[1] = toLitCond(po_cnf[po_idx] + num_var_cnf, 0);
      assump_arr[2] = toLitCond(p_in, 0);
      assump_arr[3] = toLitCond(n_in, 1);
      int assump_idx = 4;
      for (int i = 0; i < npi; i++)
      {
        int en_idx = i + 2 * num_var_cnf + 1;
        if (i != pi_idx)
        {
          assump_arr[assump_idx] = toLitCond(en_idx, 0);
          assump_idx += 1;
        }
        // else
        //   en[0] = toLitCond(en_idx,1);
      }
      int sat_result = sat_solver_solve(sat_init, assump_arr, assump_arr + assump_num, 0, 0, 0, 0);
      if (sat_result == l_True)
      {
        // pos_u[pi_idx] = false;
        int p_id = fanin_order_2_id[pi_idx] - 1;
        pos_u[p_id] = false;
      }
    }
    for (int i = 0; i < o_npi; i++)
    {
      bin_u[i] = (!pos_u[i] && !neg_u[i]);
    }

    if(neg_output){
				vector<bool> tmp = neg_u;
				neg_u = pos_u;
				pos_u = tmp;
		}

    string pos_str, neg_str, bin_str;

    for (fanin_it = fanin_map.begin(); fanin_it != fanin_map.end(); fanin_it++, j++)
    {
      // int order = fanin_id_2_order[fanin_it->first];
      int order = fanin_it->first - 1;
      // cout<<order<<endl;
      // cout<<fanin_it->first<<endl;
      // cout<<order<<endl;
      if (pos_u[order])
      {
        pos_str += fanin_it->second;
        pos_str += ",";
        // cout<<pos_str<<endl;
      }
      if (neg_u[order])
      {
        neg_str += fanin_it->second;
        neg_str += ",";
      }
      if (bin_u[order])
      {
        bin_str += fanin_it->second;
        bin_str += ",";
      }
    }
    if (pos_str.size() != 0)
    {
      pos_str.resize(pos_str.size() - 1);
      cout << "+unate inputs: ";
      cout << pos_str << endl;
    }
    if (neg_str.size() != 0)
    {
      // neg_str.pop_back();
      neg_str.resize(neg_str.size() - 1);
      cout << "-unate inputs: ";
      cout << neg_str << endl;
    }
    if (bin_str.size() != 0)
    {
      // bin_str.pop_back();
      bin_str.resize(bin_str.size() - 1);
      cout << "binate inputs: ";
      cout << bin_str << endl;
    }
  }
  Cnf_DataFree(cnf_pos_obj);
  Cnf_DataFree(cnf_neg_obj);
  sat_solver_delete(sat_init);
}

void Lsv_NtkPrint_pounate(Abc_Ntk_t *pNtk){

  Abc_Obj_t *pObj;
  int j;
  Abc_NtkForEachPo(pNtk, pObj, j)
  {
    // cout<<Abc_ObjName(pObj)<<endl;
    char* s = Abc_ObjName(pObj);
    int fUseAllCis = 0;
    // fanout_map.push_back(s);
    Abc_Obj_t * pNode = Abc_NtkFindNode(pNtk,Abc_ObjName(pObj));
    Abc_Ntk_t * ont_output_ntk = Abc_NtkCreateCone(pNtk,pNode,s,fUseAllCis);
    bool neg_po = (pObj -> fCompl0 + pObj -> fCompl1 == 1);
    // if(pObj -> fCompl0 == 1 && pObj -> fCompl1 == 0 && pNode -> fCompl0 == 0 && pNode -> fCompl1 == 0){
    //   cout<<Abc_ObjName(pObj)<<endl;
    // }
    // cout<<"po obj compl0: "<<pObj -> fCompl0<<" compl1: "<<pObj -> fCompl1<<endl;
    // cout<<"po node compl0: "<<pNode -> fCompl0<<" compl1: "<<pNode -> fCompl1<<endl;
    Lsv_NtkPrint_pounate_one_output(ont_output_ntk, pNtk, neg_po);
  }
}

int Lsv_CommandPrint_poUnate(Abc_Frame_t *pAbc, int argc, char **argv)
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
  Lsv_NtkPrint_pounate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}