#!/bin/bash

# load SageMath
cd ~/Drinfeld-modular-form-generators
module load app/SageMath/9.2

# run the computation
sage cuspExpansions.sage $1 $2

# email that the computation is complete
mail -s "q=$1, deg=$2 computation complete" liambaker@sun.ac.za