#!/bin/bash

# load SageMath
cd ~/Drinfeld-modular-form-generators
module load app/SageMath/9.2

# run the computation
sage cuspExpansions.sage 2 3 hypo

# email that the computation is complete
echo "" | mail -s "q=2, deg=3 hypothetical computation complete" liambaker@sun.ac.za
