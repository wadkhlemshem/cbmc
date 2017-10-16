#include <math.h>



#define K_X_SIZE (9)

#define K_Y_SIZE (6)

#define M_SCH_MIN (2)

#define M_SCH_MAX (4)

#define ALPHA_SCH_MIN (0)

#define ALPHA_SCH_MAX (0.3491f)



typedef enum LookupMethods{

  EXTRAPOLATION,

  USE_INPUT_NEAREST

} LookupMethods_t;



typedef struct Lookup_Map_2D_data {

  float rowVect[K_X_SIZE];

  float colVect[K_Y_SIZE];

  float table[K_X_SIZE][K_Y_SIZE];

  LookupMethods_t lookUpMeth;

} Lookup_Map_2D_data_t;



typedef struct Calc_gains_blk_flattened_data {

  Lookup_Map_2D_data_t i_look1;

  Lookup_Map_2D_data_t i_look2;

  Lookup_Map_2D_data_t i_look3;

  Lookup_Map_2D_data_t i_look4;

  float K_M_sch_x[K_X_SIZE];

  float K_alpha_sch_y[K_Y_SIZE];

  float Ka_map[K_X_SIZE][K_Y_SIZE];

  float Kg_map[K_X_SIZE][K_Y_SIZE];

  float K_map[K_X_SIZE][K_Y_SIZE];

  float Ki_map[K_X_SIZE][K_Y_SIZE];

} Calc_gains_blk_flattened_data_t;



float interpolate(float xleft, float xright, float yleft, float yright, float x)

{

  return yleft + (((yright - yleft) / (xright - xleft)) * (x - xleft));

}



float lookup2DCalc(float rowVector[K_X_SIZE], float colVector[K_Y_SIZE], float table[K_X_SIZE][K_Y_SIZE], LookupMethods_t lookUpMeth, float rowIn, float colIn)

{

  int ridx;

  int cidx;

  float left;

  float right;

  float res;



  for ( ridx = 0 ; ridx < 2U; ridx++ )

  {

    if ( rowVector[ridx + 1U] > rowIn )

                        break;

  }



  for ( cidx = 0 ; cidx < 2U; cidx++ )

  {

    if ( colVector[cidx + 1U] > colIn )

      break;

  }



  if ( (lookUpMeth == EXTRAPOLATION))

  {

    left = interpolate(rowVector[ridx], rowVector[ridx + 1], table[ridx][cidx], table[ridx + 1][cidx], rowIn);

    right = interpolate(rowVector[ridx], rowVector[ridx + 1], table[ridx][cidx + 1], table[ridx + 1][cidx + 1], rowIn);

    res = interpolate(colVector[cidx], colVector[cidx + 1], left, right, colIn);

  } else if (lookUpMeth == USE_INPUT_NEAREST) {

    if ( fabs(rowVector[ridx + 1] - rowIn) < fabs(rowIn - rowVector[ridx])) {

      ridx = ridx + 1;

    }

    if ( fabs(colVector[cidx + 1] - colIn) < fabs(colIn - colVector[cidx])) {

      cidx = cidx + 1;

    }

    res = table[ridx][cidx];

  } else {

    res = table[ridx + 1][cidx + 1];

  }

  return res;

}



void Lookup_Map_2D_execute(Lookup_Map_2D_data_t *___data, float x0, float y0, float *res)

{

  (*res) = ((float )(lookup2DCalc(___data->rowVect, ___data->colVect, ___data->table, ___data->lookUpMeth, x0, y0)));

}



void blk_flattened_execute(Calc_gains_blk_flattened_data_t *___data, float alpha, float speed)

{

  float look1_res;

  float look2_res;

  float look3_res;

  float look4_res;



  Lookup_Map_2D_execute(&(___data->i_look3), speed, alpha, &look3_res);

  Lookup_Map_2D_execute(&(___data->i_look4), speed, alpha, &look4_res);

  Lookup_Map_2D_execute(&(___data->i_look1), speed, alpha, &look1_res);

  Lookup_Map_2D_execute(&(___data->i_look2), speed, alpha, &look2_res);

}
