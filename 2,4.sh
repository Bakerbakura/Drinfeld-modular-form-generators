#!/bin/bash

# load SageMath
cd ~/Drinfeld-modular-form-generators
module load app/SageMath/9.2

# run the computation
sage cuspExpansions.sage 2 4

# email that the computation is complete
mail -s "q=2, deg=4 computation complete" liambaker@sun.ac.za
