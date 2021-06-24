#!/bin/bash

# load SageMath
cd ~/Drinfeld-modular-form-generators
module load app/SageMath/9.2

# run the computation
sage cuspExpansions.sage 4 2

# email that the computation is complete
echo "" | mail -s "q=4, deg=2 computation complete" liambaker@sun.ac.za
