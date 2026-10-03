/* Process-local allocation diagnostic, not a runtime optimization.
 * cc -shared -fPIC -O2 disable-thp.c -o /tmp/disable-thp.so
 * LD_PRELOAD=/tmp/disable-thp.so <benchmark command>
 */
#include <stdlib.h>
#include <sys/prctl.h>

__attribute__((constructor)) static void disable_thp(void) {
    if (prctl(PR_SET_THP_DISABLE, 1, 0, 0, 0) != 0)
        abort();
}
