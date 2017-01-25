# ASP-DPOP
# AAAI15
# This README file is under construction...

Frodo format based-instance files for experimental result.
Smartgrid: 13, 34, 37, 123 agents
Random network: varying each domain size |D|, number of variables |X|, constraint density (p1), and constraint tightness (p2), 

Requirements:
  - Sicstus 
  - gringo
  - clasp
  
Command to run:
sicstus -l xmldcopv31.pl --goal "tiep(prefix_of_input_file),halt."
