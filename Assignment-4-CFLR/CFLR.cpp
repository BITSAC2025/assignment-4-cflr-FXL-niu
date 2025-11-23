/**
 * CFLR.cpp
 * @author kisslune 
 */

 #include "A4Header.h"

 using namespace SVF;
 using namespace llvm;
 using namespace std;
 
 int main(int argc, char **argv)
 {
     auto moduleNameVec =
             OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                      "[options] <input-bitcode...>");
 
     LLVMModuleSet::buildSVFModule(moduleNameVec);
 
     SVFIRBuilder builder;
     auto pag = builder.build();
     pag->dump();
 
     CFLR solver;
     solver.buildGraph(pag);
     // TODO: complete this method
     solver.solve();
     solver.dumpResult();
 
     LLVMModuleSet::releaseLLVMModuleSet();
     return 0;
 }
 
 
 void CFLR::solve()
 {
     // TODO: complete this function. The implementations of graph and worklist are provided.
     //  You need to:
     //  1. implement the grammar production rules into code;
     //  2. implement the dynamic-programming CFL-reachability algorithm.
     //  You may need to add your new methods to 'CFLRGraph' and 'CFLR'.
     /**********************************************************************
      * 0. 辅助 Lambda：用于添加新边（避免重复代码）
      * 功能：若边不存在，则加入图中并放入工作列表
      **********************************************************************/
     auto addCFLItem = [&](unsigned u, unsigned v, EdgeLabel label) {
         if (!graph->hasEdge(u, v, label)) {
             graph->addEdge(u, v, label);
             workList.push(CFLREdge(u, v, label));
         }
     };
 
     /**********************************************************************
      * 1. 初始化：处理 ε 产生式  (例如 V ::= ε)
      * 对图中所有节点插入：
      *   v —VF→ v
      *   v —VFBar→ v
      *   v —VA→ v
      **********************************************************************/
     std::unordered_set<unsigned> allNodes;
 
     for (auto& node : graph->getSuccessorMap())   allNodes.insert(node.first);
     for (auto& node : graph->getPredecessorMap()) allNodes.insert(node.first);
 
     for (unsigned v : allNodes) {
         addCFLItem(v, v, VF);     // VF ::= ε
         addCFLItem(v, v, VFBar);  // VFBar ::= ε
         addCFLItem(v, v, VA);     // VA ::= ε
     }
 
     /**********************************************************************
      * 2. 初始化工作列表：将图中已有的边加入 worklist
      **********************************************************************/
     auto& succMap = graph->getSuccessorMap();
     for (auto& srcItem : succMap) {
         unsigned src = srcItem.first;
         for (auto& labelItem : srcItem.second) {
             EdgeLabel label = labelItem.first;
             for (unsigned dst : labelItem.second) {
                 workList.push(CFLREdge(src, dst, label));
             }
         }
     }
 
     /**********************************************************************
      * 3. 主循环：不断处理工作列表中的 CFLR 边
      **********************************************************************/
     while (!workList.empty()) {
 
         CFLREdge edge = workList.pop();
         unsigned  v_i = edge.src;
         unsigned  v_j = edge.dst;
         EdgeLabel X   = edge.label;
 
         /******************************************************************
          * === 一元产生式处理: A ::= X ===
          ******************************************************************/
         if (X == Copy)    addCFLItem(v_i, v_j, VF);     // VF ::= Copy
         if (X == CopyBar) addCFLItem(v_i, v_j, VFBar);  // VFBar ::= CopyBar
 
         /******************************************************************
          * === 二元产生式（顺向匹配）A ::= X Y ===
          * 当前边为 X: v_i —X→ v_j
          * 寻找 v_j 的后继边：v_j —Y→ v_k
          ******************************************************************/
         if (graph->getSuccessorMap().count(v_j)) {
             auto& succs_vj = graph->getSuccessorMap()[v_j];
 
             for (auto& Y_item : succs_vj) {
                 EdgeLabel Y = Y_item.first;
                 for (unsigned v_k : Y_item.second) {
 
                     // 以下对应各种 A ::= X Y 的规则
                     if (X == VFBar && Y == AddrBar) addCFLItem(v_i, v_k, PT);      // PT ::= VFBar AddrBar
                     if (X == VF    && Y == VF)     addCFLItem(v_i, v_k, VF);      // VF ::= VF VF
                     if (X == SV    && Y == Load)   addCFLItem(v_i, v_k, VF);      // VF ::= SV Load
                     if (X == PV    && Y == Load)   addCFLItem(v_i, v_k, VF);      // VF ::= PV Load
                     if (X == Store && Y == VP)     addCFLItem(v_i, v_k, VF);      // VF ::= Store VP
                     if (X == VFBar && Y == VFBar)  addCFLItem(v_i, v_k, VFBar);   // VFBar ::= VFBar VFBar
                     if (X == LoadBar && Y == SVBar) addCFLItem(v_i, v_k, VFBar);  // VFBar ::= LoadBar SVBar
                     if (X == LoadBar && Y == VP)   addCFLItem(v_i, v_k, VFBar);   // VFBar ::= LoadBar VP
                     if (X == PV && Y == StoreBar)  addCFLItem(v_i, v_k, VFBar);   // VFBar ::= PV StoreBar
                     if (X == LV && Y == Load)      addCFLItem(v_i, v_k, VA);      // VA ::= LV Load
                     if (X == VFBar && Y == VA)     addCFLItem(v_i, v_k, VA);      // VA ::= VFBar VA
                     if (X == VA && Y == VF)        addCFLItem(v_i, v_k, VA);      // VA ::= VA VF
 
                     // 之前遗漏的规则
                     if (X == Addr && Y == VF)      addCFLItem(v_i, v_k, PTBar);   // PTBar ::= Addr VF
                     if (X == Store && Y == VA)     addCFLItem(v_i, v_k, SV);      // SV ::= Store VA
                     if (X == VA && Y == StoreBar)  addCFLItem(v_i, v_k, SVBar);   // SVBar ::= VA StoreBar
                     if (X == PTBar && Y == VA)     addCFLItem(v_i, v_k, PV);      // PV ::= PTBar VA
                     if (X == VA && Y == PT)        addCFLItem(v_i, v_k, VP);      // VP ::= VA PT
                     if (X == LoadBar && Y == VA)   addCFLItem(v_i, v_k, LV);      // LV ::= LoadBar VA
                 }
             }
         }
 
         /******************************************************************
          * === 二元产生式（逆向匹配）A ::= Y X ===
          * 当前边为 X: v_i —X→ v_j
          * 寻找前驱边：v_k —Y→ v_i
          ******************************************************************/
         if (graph->getPredecessorMap().count(v_i)) {
             auto& preds_vi = graph->getPredecessorMap()[v_i];
 
             for (auto& Y_item : preds_vi) {
                 EdgeLabel Y = Y_item.first;
                 for (unsigned v_k : Y_item.second) {
 
                     // A ::= Y X 的规则
                     if (Y == Addr && X == VF)       addCFLItem(v_k, v_j, PTBar);   // PTBar ::= Addr VF
                     if (Y == Store && X == VA)      addCFLItem(v_k, v_j, SV);      // SV ::= Store VA
                     if (Y == VA && X == StoreBar)   addCFLItem(v_k, v_j, SVBar);   // SVBar ::= VA StoreBar
                     if (Y == PTBar && X == VA)      addCFLItem(v_k, v_j, PV);      // PV ::= PTBar VA
                     if (Y == VA && X == PT)         addCFLItem(v_k, v_j, VP);      // VP ::= VA PT
                     if (Y == LoadBar && X == VA)    addCFLItem(v_k, v_j, LV);      // LV ::= LoadBar VA
 
                     // 对称补全的规则（之前遗漏）
                     if (Y == VFBar && X == AddrBar) addCFLItem(v_k, v_j, PT);      // PT ::= VFBar AddrBar
                     if (Y == VF && X == VF)         addCFLItem(v_k, v_j, VF);      // VF ::= VF VF
                     if (Y == SV && X == Load)       addCFLItem(v_k, v_j, VF);      // VF ::= SV Load
                     if (Y == PV && X == Load)       addCFLItem(v_k, v_j, VF);      // VF ::= PV Load
                     if (Y == Store && X == VP)      addCFLItem(v_k, v_j, VF);      // VF ::= Store VP
                     if (Y == VFBar && X == VFBar)   addCFLItem(v_k, v_j, VFBar);   // VFBar ::= VFBar VFBar
                     if (Y == LoadBar && X == SVBar) addCFLItem(v_k, v_j, VFBar);   // VFBar ::= LoadBar SVBar
                     if (Y == LoadBar && X == VP)    addCFLItem(v_k, v_j, VFBar);   // VFBar ::= LoadBar VP
                     if (Y == PV && X == StoreBar)   addCFLItem(v_k, v_j, VFBar);   // VFBar ::= PV StoreBar
                     if (Y == LV && X == Load)       addCFLItem(v_k, v_j, VA);      // VA ::= LV Load
                     if (Y == VFBar && X == VA)      addCFLItem(v_k, v_j, VA);      // VA ::= VFBar VA
                     if (Y == VA && X == VF)         addCFLItem(v_k, v_j, VA);      // VA ::= VA VF
                 }
             }
         }
     }
 }