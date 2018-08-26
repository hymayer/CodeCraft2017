#include "deploy.h"
#include <stdio.h>

#include "solution.h"
#include "solution3.h"

#include <string>

using namespace cdn;

void deploy_server(char * topo[MAX_EDGE_NUM], int line_num,char * filename)
{
    Instance *ins = new Instance(topo);
    Solution3 *sol = new Solution3(ins);
    
    std::string strResult;

    cdnStatus ret = CDN_OK;
    
    ret = sol->LocalSearch3();
    if (ret != CDN_OK)
    {
        
    }
    
    sol->GetResult(strResult);
    
    write_result(strResult.c_str(), filename);

    delete sol;
    delete ins;
}
