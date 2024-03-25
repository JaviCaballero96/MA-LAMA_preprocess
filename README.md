
## --- If you want to use MA-LAMA, please refer to the MA-LAMA repository ---

This project composes the phase TWO of the MA-LAMA planner, it is only meant to be downloaded separately for developement purposes.
More precisely, this module is used as a data processing phase between the translate and search phases that generalizes variables and calculates graphs and interactions.

To launch, it takes as an input the output.sas file(s) from the translate module: 

./preprocess <output.sas>

It is launched one time for each agent and generates the file:
  - output_preproagent[n_agnet]: one for each agent, contains the processed metric, variables, shared variables, initial state, goals, operators, and causal graph.
