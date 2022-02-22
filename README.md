# Antecedent Moisture Modeling (AMM) for PCSWMM
Antecedent Moisture Modeling (AMM) is a state-of-the-art hydrologic method for modeling flow-rainfall responses which depend on moisture conditions. Unlike many other hydrologic methods which model the percent rainfall capture as a constant, AMM can model systems where the percent rainfall capture changes with back-to-back storms and over different seasons.

AMM has especially found a use in modeling sanitary sewer infiltration and inflow (I/I), which often depends strongly on moisture conditions. When compared with other methods such as the RTK Unit Hydrograph Method, for catchments that are dependent on antecedent moisture, AMM can predict flows with much greater accuracy. 

![Picture1](https://user-images.githubusercontent.com/20068871/155231175-e6473956-0ec4-4ffc-b56c-897344487486.png)

The included script is a user-friendly way to get started quickly with AMM inside the PCSWMM hydraulic modeling software.

## How to Use

The included CalculateAMM.py script should be loaded into the script window of PCSWMM. The script has been tested for PCSWMM 7.4 but should be widely compatible between versions. The user settings section of the script should be reviewed. The first run of the script will set up an "AMM_Subcatchments" polygon layer with the appropriate attributes and open it in the model. Draw or import your polygons representing the subcatchments, complete the needed attributes, then run the script again to calculate results.

See the User Documentation section of the script for additional info.

## Questions

Do you have questions about how to use this script or how to use AMM generally? Head on over to the AMM Users group and start a new conversation there. We would love to help you out!

https://groups.google.com/u/1/g/amm-users

## Contributions

Do you have suggestions for how to improve the script? Start a conversation on the AMM Users group or submit a pull request here. This is a pretty small project, but any community contributions are appreciated and welcome.

## Additional Resources

The AMM equations were presented at the ICWMM Conference in March 2021 by Robert Czachorski. The accompanying paper is here:

https://www.chijournal.org/C482

A reparameterized version intended to be more user-friendly for calibration was presented at the ICWMM Conference in March 2022 by David Edgren, Robert Czachorski, and Willie Gonwa (paper pending). This script is an implementation of the March 2022 presentation.

Check out the Antecedent Moisture Model Learning Library for technical papers and an example spreadsheet of the AMM Method:

https://h2ometrics.com/antecedent-moisture-model/

## Acknowledgements

Many thanks to RJN Group which is generously allowing this script to be open-sourced so others in the hydraulic modeling community can try out AMM.

Thanks to Robert Czachorski and Willie Gonwa for their longstanding work on AMM and for our many collaboration sessions debating small details to make AMM as user-friendly as possible.

Thanks also to Hailiang Shen at CHI, whose example script for implementing a custom hydrologic method served as the foundation for this script.
