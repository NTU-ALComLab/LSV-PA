extern "C" {
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
}

extern void init(Abc_Frame_t* pAbc);
extern void destroy(Abc_Frame_t* pAbc);

static Abc_FrameInitializer_t lsvInitializer = {
    init,
    destroy,
    NULL,
    NULL,
    NULL,
    NULL
};

struct LsvPackageRegister {
    LsvPackageRegister() { Abc_FrameAddInitializer(&lsvInitializer); }
} lsvPackageRegister;
