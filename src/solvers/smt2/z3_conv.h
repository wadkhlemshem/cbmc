/*******************************************************************\

Module: Z3 C++ API Backend

Author: Johanan Wahlang, wadkhlemshem@gmail.com
        Manasij Mukherjee, manasij7479@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_Z3_CONV_H
#define CPROVER_SOLVERS_SMT2_Z3_CONV_H

#include <fstream>
#include <set>

#include <util/hash_cont.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/byte_operators.h>
#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>
#include <z3++.h>

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

#endif // CPROVER_SOLVERS_SMT2_Z3_CONV_H
