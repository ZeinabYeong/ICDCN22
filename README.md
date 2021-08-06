# ICDCN22

-----   TLA+ TOOLBOX   -----

To verify a specification written in TLA+, you will need the TLA+ toolbox. 
It is an IDE that allows you to create and edit a specification, and run : the PlusCal translator, the model-checker TLC, and the proof system TLAPS. 

To install and download the tool, please refer to the following link :
https://lamport.azurewebsites.net/tla/toolbox.html

The version of TLA+ Toolbox used in this study is :
Version 1.7.1 of 31 December 2020 that includes:
  - SANY Version 2.2 of 20 April 2020
  - TLC Version 2.16 of 31 December 2020
  - PlusCal Version 1.11 of 31 December 2020
  - TLATeX Version 1.0 of 20 September 2017
  - TLAPS Version 1.4.5 of February 2020
  

Steps for proving safety (Consistency):
1) Open the tla file in the TLA+ toolbox.
2) Right-click on the theorem you want to prove.
3) Click on "TLA Proof Manager" then on "Prove step or Module".
4) The theorem turns green when it is proved and turns red when it is not proved.

Steps for checking liveness (Ownership and Retrieving):
1) Open the tla file in the TLA+ toolbox.
2) Create a model by right-clicking on the folder of the file.
3) Click on "New model" and give a name to the model.
4) Specify the value of NTxs and Correct in the "what is the model?" section, e.g. NTxs <- 3 and Correct <- {1, 3, 6, 7} (this execution contains 2 Byzantine).
5) In the section "what to check?" add the properties (by giving the name) you want to check (uncheck Deadlock). Safety property is added in "Invariants" section and liveness properties are added in "Properties" section. 
6) Run TLC on the model by clicking on the green button bellow "Model Overview".
7) TLC raises an error message if the property is violated. 
