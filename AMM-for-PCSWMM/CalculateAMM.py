# tags: MapToolsSWMM
# file: CalculateAMM
# name: Calculate AMM
# description: Calculate Antecedent Moisture Model (AMM) hydrology and output results to linked model inflow file
#
# Written by David Edgren, RJN Group
# Thanks to Hailiang Shen, Computational Hydraulics International (CHI)
#
# Version 1.01
# 2022-03-14
# Updated based on updated equations and terminology
# Added a base component
# Added support for calculation of historical temperatures from timeseries
# Added option to save more outputs, including multiple components
# Improved user settings and documentation
# Releasing open source!


### USER SETTINGS ###

# Set to True to run SWMM hydraulic model run automatically after AMM calcs
_run_hydraulics = False

# Calc timstep in minutes. If set to 0 will default to "Runoff: wet weather" time step
_calc_step_min = 0

# If set to True this uses historical temperature data from a SWMM Time Series
# If set to False this uses user-defined monthly seasonal averages
_use_temp_timeseries = False

# Name of SWMM Time Series containing temperatures
# This will not be used if _use_temp_timeseries is set to False
_temp_timeseries = "AMM_Temps"

# Average temperature in degrees for each month
# This will not be used if _use_temp_timeseries is set to True
_tempDict = {
    1: 23.4,
    2: 27.1,
    3: 39,
    4: 49.9,
    5: 61.3,
    6: 70.3,
    7: 73.1,
    8: 71.5,
    9: 65.7,
    10: 53.4,
    11: 40.3,
    12: 30.1,
}

# When set to True all outputs are saved to .tsb file for later viewing - good for calibration
# When set to False only outputs Total Flow - quickest option
_full_tsb_detail = True

### END USER SETTINGS ###


### USER DOCUMENTATION ###
"""
This script is an implemention of the Antecedent Moisture Modeling (AMM) method. This
method was presented at the ICWMM Conference in March 2021 by Robert Czachorski
(https://www.chijournal.org/C482). A reparameterized version intended to be more user-
friendly for calibration was presented at the ICWMM Conference in March 2022 by David
Edgren, Robert Czachorski, and Willie Gonwa (paper pending). This script is an
implementation of the March 2022 presentation.

For more details on AMM visit www.flowprediction.com.

For questions or discussion on AMM join the AMM Users group:
groups.google.com/u/1/g/amm-users.


This script can be loaded into PCSWMM by copying and pasting into the PCSWMM editor.
Alternatively, it can be imported through the PCSWMM script editor.

When the script is run it will check if an AMM_Subcatchments layer is already present in
the current model. If it is not able to detect one (eg. the first time you run this
script for a model) it will helpfully offer to create a new one for you, which it will
set up with the appropriate attributes and save as a .shp file in the model directory in
a folder with a _files suffix. All AMM subcatchments should be created in the
AMM_Subcatchments layer and parameters should be assigned to each. After the
AMM_Subcatchments layer has been set up run the script again to run calculation.


This script creates several files, all of which are saved in the model directory in a
folder with a _files suffix. The AMM_Subcatchments.shp file contains all AMM polygons
with corresponding AMM parameters as attributes. The AMM_Subcatchments_Inflow.txt file
is an INFLOWS file compatible with EPA SWMM. The AMM_Subcatchments.tsb file is a PCSWMM
binary timeseries file for viewing results in the PCSWMM Graph panel.

Each scenario should reference its own AMM_Subcatchments.shp file in an appropriately
named _files folder. The _files convention permits the AMM data to easily follow the
model during Packing and Unpacking.

After saving a model with AMM subcatchments as a new scenario best practice is to:
1) close the old AMM_Subcatchments layer by right-clicking it in the Layers list,
2) manually copying the AMM_Subcatchments.shp file from the OldScenarioName_files folder
to a NewScenarioName_files folder, and
3) open the duplicated AMM_Subcatchments.shp as a layer in the new scenario.

If a model is renamed the _files folder should also be renamed.


This script supports two methods to input the temperatures used in Level 3. If
_use_actual_temps is set to True the script will use temps provided in a SWMM timeseries.
Alternatively, seasonal average monthly temperatures can be input in the user settings.
There are pros and cons to either approach and extensive testing has not been done to
compare the two methods.


To be consistent with the SWMM engine and many data tools it is assumed input rain data
in Volume or Intensity formats follow the "start-of-interval" convention, meaning that
each rainfall intensity or depth is assumed to occur at the start of its associated
date/time value and span a period of time equal to the gage's recording interval.


This script has been designed for maximum compatability, so it intentionally has a large
number of calibratable parameters. In general it is not recommended to leave all these
parameters free during calibration.

It has 4 total components: Fast, Medium, and Slow are standard components while Base is
a 2-level Baseflow component. A sensible default is to use the Fast, Medium, and Base
components. In this case Slow parameters may be safely left at zero.

This script supports the sigmoid function for Level 3 with split Cold SHCF parameters
for Fall and Spring. The Spring Cold SHCF applies between Jan. 1 and July 15. The Fall
Cold SHCF applies between July 16 and Dec. 31. The linear SHCF equation is not currently
supported.
"""
### END USER DOCUMENTATION ###


import copy
import datetime
import math
import os
import re
from collections import defaultdict

_nodes = pcpy.SWMM.Nodes
_gages = pcpy.SWMM.Raingages
_options = pcpy.SWMM.Options
_flow_unit = _options.FlowUnits
_unit_system = {
    "CMS": "METRIC",
    "LPS": "METRIC",
    "MLD": "METRIC",
    "CFS": "IMPERIAL",
    "GPM": "IMPERIAL",
    "MGD": "IMPERIAL",
}[_flow_unit]
# Define measurement names and metadata: 0) which tsb function to associate with, and
#    1) whether to concatenate meas_name to location name
#       (which is necessary for uniqueness but means you can't graph directly from the map)
if _full_tsb_detail is True:
    _meas_names = {
        "Runoff_Total": [0, False],
        "Runoff_Fast": [0, True],
        "Runoff_Med": [0, True],
        "Runoff_Slow": [0, True],
        "Runoff_Base": [0, True],
        "PC_Fast": [1, True],
        "PC_Med": [1, True],
        "PC_Slow": [1, True],
        "PC_Base": [1, True],
        "SHCF_Fast": [2, True],
        "SHCF_Med": [2, True],
        "SHCF_Slow": [2, True],
        "Rain": [3, False],
        "Temps": [4, False],
    }
else:
    _meas_names = {"Runoff_Total": [0, False]}
_start_t, _end_t = 0, 0  # Save routing times in global var
_all_t = []
_conformed_rain = {}
_common_temps = []
_already_calced_subs = {}
_Q_conv_factor = {
    "CMS": 1.0,
    "LPS": 0.001,
    "MLD": 1000 / 86400.0,
    "CFS": 0.028316847,
    "GPM": 0.000063090196666667,
    "MGD": 0.0438126364,
}[
    _flow_unit
]  # To CMS
_SHCF_conv_factor = {"METRIC": 1000, "IMPERIAL": 39.37}[_unit_system]  # To 1/m
_rain_conv_factor = {"METRIC": 0.001, "IMPERIAL": 0.0254}[_unit_system]  # To m


class AMMSub:
    """Calculates results for a single AMM subcatchment."""

    def __init__(self, entity):
        # Read data from entity, validate it, and convert unit to metric base units
        self.name = entity["Name"]
        if self.name == "":
            raise Exception("All AMM Subcatchments must have names!")

        self.outlet = entity["Outlet"]
        if self.outlet not in _nodes:
            raise Exception('Sub "%s" must have a valid outlet' % self.name)

        if entity["ScaleArea"] == "True":
            entity["Area"] = (
                entity.Geometry.Area
                * {"METRIC": 1e-4, "IMPERIAL": 2.2957e-5}[_unit_system]  # To ha or ac
            )

        self.area = float(entity["Area"])
        if self.area <= 0:
            raise Exception('Area of sub "%s" must be positive' % self.name)
        self.area *= {"METRIC": 1e4, "IMPERIAL": 4046.86}[_unit_system]  # To m2

        if entity["RainGage"] not in _gages:
            raise Exception('Sub "%s" must have a valid assigned rain gage' % self.name)
        self.gage = _gages[entity["RainGage"]]
        if self.gage.DataSource not in ["TIMESERIES"]:
            raise Exception(
                'Rain gage "%s": this script currently only supports the TIMESERIES data source'
                % self.gage.name
            )

        self.RDFast = float(entity["RDFast"])
        if self.RDFast < 0:
            raise Exception('RDFast of sub "%s" may not be negative' % self.name)
        self.RDFast /= 100  # Convert from % to whole number
        self.RDMed = float(entity["RDMed"])
        if self.RDMed < 0:
            raise Exception('RDMed of sub "%s" may not be negative' % self.name)
        self.RDMed /= 100  # Convert from % to whole number
        self.RDSlow = float(entity["RDSlow"])
        if self.RDSlow < 0:
            raise Exception('RDSlow of sub "%s" may not be negative' % self.name)
        self.RDSlow /= 100  # Convert from % to whole number

        self.HotRBase = float(entity["HtRBase"])
        if self.HotRBase < 0:
            raise Exception('Base Hot R of sub "%s" may not be negative' % self.name)
        self.HotRBase /= 100  # Convert from % to whole number
        self.SpringColdRBase = float(entity["SpClRB"])
        if self.SpringColdRBase < 0:
            raise Exception(
                'Base Spring Cold R of sub "%s" may not be negative' % self.name
            )
        self.SpringColdRBase /= 100  # Convert from % to whole number
        self.FallColdRBase = float(entity["FlClRB"])
        if self.FallColdRBase < 0:
            raise Exception(
                'Base Fall Cold R of sub "%s" may not be negative' % self.name
            )
        self.FallColdRBase /= 100  # Convert from % to whole number

        self.TPFast = (
            float(entity["TPFast"]) * 60 / _calc_step_min
        )  # From hours to number of timesteps
        if self.TPFast < 0:
            raise Exception('TPFast of sub "%s" may not be negative' % self.name)
        self.TPMed = (
            float(entity["TPMed"]) * 60 / _calc_step_min
        )  # From hours to number of timesteps
        if self.TPMed < 0:
            raise Exception('TPMed of sub "%s" may not be negative' % self.name)
        self.TPSlow = (
            float(entity["TPSlow"]) * 60 / _calc_step_min
        )  # From hours to number of timesteps
        if self.TPSlow < 0:
            raise Exception('TPSlow of sub "%s" may not be negative' % self.name)
        self.TPBase = (
            float(entity["TPBase"]) * 60 / _calc_step_min
        )  # From hours to number of timesteps
        if self.TPBase < 0:
            raise Exception('TPBase of sub "%s" may not be negative' % self.name)

        self.HHLFast = float(entity["HHLFast"])
        if self.HHLFast <= 0 and self.RDFast > 0:
            raise Exception('HHLFast of sub "%s" must be positive' % self.name)
        self.HHLFast *= 3600  # From hours to seconds
        self.HHLMed = float(entity["HHLMed"])
        if self.HHLMed <= 0 and self.RDMed > 0:
            raise Exception('HHLMed of sub "%s" must be positive' % self.name)
        self.HHLMed *= 3600  # From hours to seconds
        self.HHLSlow = float(entity["HHLSlow"])
        if self.HHLSlow <= 0 and self.RDSlow > 0:
            raise Exception('HHLSlow of sub "%s" must be positive' % self.name)
        self.HHLSlow *= 3600  # From hours to seconds
        self.HHLBase = float(entity["HHLBase"])
        if (
            self.HHLBase <= 0
            and max(self.HotRBase, self.SpringColdRBase, self.FallColdRBase) > 0
        ):
            raise Exception('HHLBase of sub "%s" must be positive' % self.name)
        self.HHLBase *= 3600  # From hours to seconds

        self.RW0Fast = float(entity["RW0Fast"])
        if self.RW0Fast < 0:
            raise Exception(
                'Fast Initial Wet Capture Fraction of sub "%s" may not be negative'
                % self.name
            )
        self.RW0Med = float(entity["RW0Med"])
        if self.RW0Med < 0:
            raise Exception(
                'Medium Initial Wet Capture Fraction of sub "%s" may not be negative'
                % self.name
            )
        self.RW0Slow = float(entity["RW0Slow"])
        if self.RW0Slow < 0:
            raise Exception(
                'Slow Initial Wet Capture Fraction of sub "%s" may not be negative'
                % self.name
            )

        self.AMHLFast = float(entity["AMHLFast"])
        if self.AMHLFast <= 0 and self.RDFast > 0:
            raise Exception('AMHLFast of sub "%s" must be positive' % self.name)
        self.AMHLFast *= 86400  # From days to seconds
        self.AMHLMed = float(entity["AMHLMed"])
        if self.AMHLMed <= 0 and self.RDMed > 0:
            raise Exception('AMHLMed of sub "%s" must be positive' % self.name)
        self.AMHLMed *= 86400  # From days to seconds
        self.AMHLSlow = float(entity["AMHLSlow"])
        if self.AMHLSlow <= 0 and self.RDSlow > 0:
            raise Exception('AMHLSlow of sub "%s" must be positive' % self.name)
        self.AMHLSlow *= 86400  # From days to seconds

        self.MATFast = (
            float(entity["MATFast"]) * 1440 / _calc_step_min
        )  # From days to number of timesteps
        if self.MATFast < 0:
            raise Exception('MATFast of sub "%s" may not be negative' % self.name)
        self.MATMed = (
            float(entity["MATMed"]) * 1440 / _calc_step_min
        )  # From days to number of timesteps
        if self.MATMed < 0:
            raise Exception('MATMed of sub "%s" may not be negative' % self.name)
        self.MATSlow = (
            float(entity["MATSlow"]) * 1440 / _calc_step_min
        )  # From days to number of timesteps
        if self.MATSlow < 0:
            raise Exception('MATSlow of sub "%s" may not be negative' % self.name)

        self.SATFast = (
            float(entity["SATFast"]) * 1440 / _calc_step_min
        )  # Convert from days to number of timesteps
        if self.SATFast < 0:
            raise Exception('SATFast of sub "%s" may not be negative' % self.name)
        self.SATMed = (
            float(entity["SATMed"]) * 1440 / _calc_step_min
        )  # Convert from days to number of timesteps
        if self.SATMed < 0:
            raise Exception('SATMed of sub "%s" may not be negative' % self.name)
        self.SATSlow = (
            float(entity["SATSlow"]) * 1440 / _calc_step_min
        )  # Convert from days to number of timesteps
        if self.SATSlow < 0:
            raise Exception('SATSlow of sub "%s" may not be negative' % self.name)
        self.SATBase = (
            float(entity["SATBase"]) * 1440 / _calc_step_min
        )  # Convert from days to number of timesteps
        if self.SATBase < 0:
            raise Exception('SATBase of sub "%s" may not be negative' % self.name)

        self.HotSHCFFast = float(entity["HtSHCFFast"])
        if self.HotSHCFFast < 0:
            raise Exception('Fast Hot SHCF of sub "%s" may not be negative' % self.name)
        self.HotSHCFFast *= _SHCF_conv_factor  # To 1/m
        self.HotSHCFMed = float(entity["HtSHCFMed"])
        if self.HotSHCFMed < 0:
            raise Exception(
                'Medium Hot SHCF of sub "%s" may not be negative' % self.name
            )
        self.HotSHCFMed *= _SHCF_conv_factor  # To 1/m
        self.HotSHCFSlow = float(entity["HtSHCFSlow"])
        if self.HotSHCFSlow < 0:
            raise Exception('Slow Hot SHCF of sub "%s" may not be negative' % self.name)
        self.HotSHCFSlow *= _SHCF_conv_factor  # To 1/m

        self.SpringColdSHCFFast = float(entity["SpClSHCFF"])
        if self.SpringColdSHCFFast < 0:
            raise Exception(
                'Fast Spring Cold SHCF of sub "%s" may not be negative' % self.name
            )
        self.SpringColdSHCFFast *= _SHCF_conv_factor  # To 1/m
        self.SpringColdSHCFMed = float(entity["SpClSHCFM"])
        if self.SpringColdSHCFMed < 0:
            raise Exception(
                'Medium Spring Cold SHCF of sub "%s" may not be negative' % self.name
            )
        self.SpringColdSHCFMed *= _SHCF_conv_factor  # To 1/m
        self.SpringColdSHCFSlow = float(entity["SpClSHCFS"])
        if self.SpringColdSHCFSlow < 0:
            raise Exception(
                'Slow Spring Cold SHCF of sub "%s" may not be negative' % self.name
            )
        self.SpringColdSHCFSlow *= _SHCF_conv_factor  # To 1/m

        self.FallColdSHCFFast = float(entity["FlClSHCFF"])
        if self.FallColdSHCFFast < 0:
            raise Exception(
                'Fast Fall Cold SHCF of sub "%s" may not be negative' % self.name
            )
        self.FallColdSHCFFast *= _SHCF_conv_factor  # To 1/m
        self.FallColdSHCFMed = float(entity["FlClSHCFM"])
        if self.FallColdSHCFMed < 0:
            raise Exception(
                'Medium Fall Cold SHCF of sub "%s" may not be negative' % self.name
            )
        self.FallColdSHCFMed *= _SHCF_conv_factor  # To 1/m
        self.FallColdSHCFSlow = float(entity["FlClSHCFS"])
        if self.FallColdSHCFSlow < 0:
            raise Exception(
                'Slow Fall Cold SHCF of sub "%s" may not be negative' % self.name
            )
        self.FallColdSHCFSlow *= _SHCF_conv_factor  # To 1/m

        self.HotTemp = float(entity["HotTemp"])
        if self.HotTemp == "":
            raise Exception('Hot Temp of sub "%s" must be defined' % self.name)
        self.ColdTemp = float(entity["ColdTemp"])
        if self.ColdTemp == "":
            raise Exception('Cold Temp of sub "%s" must be defined' % self.name)
        if self.ColdTemp >= self.HotTemp:
            raise Exception(
                'Hot Temp of sub "%s" should be greater than Cold Temp' % self.name
            )

        # Used to check if catchments are twins
        self.all_params = (
            self.gage,
            self.RDFast,
            self.RDMed,
            self.RDSlow,
            self.TPFast,
            self.TPMed,
            self.TPSlow,
            self.TPBase,
            self.HHLFast,
            self.HHLMed,
            self.HHLSlow,
            self.HHLBase,
            self.RW0Fast,
            self.RW0Med,
            self.RW0Slow,
            self.AMHLFast,
            self.AMHLMed,
            self.AMHLSlow,
            self.MATFast,
            self.MATMed,
            self.MATSlow,
            self.SATFast,
            self.SATMed,
            self.SATSlow,
            self.SATBase,
            self.HotSHCFFast,
            self.HotSHCFMed,
            self.HotSHCFSlow,
            self.HotRBase,
            self.SpringColdSHCFFast,
            self.SpringColdSHCFMed,
            self.SpringColdSHCFSlow,
            self.SpringColdRBase,
            self.FallColdSHCFFast,
            self.FallColdSHCFMed,
            self.FallColdSHCFSlow,
            self.FallColdRBase,
            self.HotTemp,
            self.ColdTemp,
        )
        self.results = {
            meas_name: [None] * len(_all_t) for meas_name in _meas_names.keys()
        }

    def AMM_run(self):
        # Calculate derived parameters
        self.SFFast = self.calc_decay_constant(self.HHLFast)
        self.SFMed = self.calc_decay_constant(self.HHLMed)
        self.SFSlow = self.calc_decay_constant(self.HHLSlow)
        self.SFBase = self.calc_decay_constant(self.HHLBase)

        self.AMRFFast = self.calc_decay_constant(self.AMHLFast)
        self.AMRFMed = self.calc_decay_constant(self.AMHLMed)
        self.AMRFSlow = self.calc_decay_constant(self.AMHLSlow)

        self.x0 = (self.ColdTemp + self.HotTemp) / 2
        self.k = 4.7964 / (self.ColdTemp - self.HotTemp)

        self.maxMA = (
            int(
                math.floor(
                    max(
                        [
                            self.TPFast,
                            self.TPMed,
                            self.TPSlow,
                            self.TPBase,
                            self.MATFast,
                            self.MATMed,
                            self.MATSlow,
                            self.SATFast,
                            self.SATMed,
                            self.SATSlow,
                            self.SATBase,
                        ]
                    )
                )
            )
            + 1
        )  # Maximum number of pre-simulation values needed for moving averages on first
        timestep

        # If rain gage has already been used then use the conformed rainfall that has
        # already been computed
        # Otherwise conform the rainfall to the appropriate start date, end date,
        # frequency, and a volume rain format
        if self.gage.Name not in _conformed_rain:
            _conformed_rain[self.gage.Name] = conform_rainfall(self.gage)

        # Assume zero precipitation prior to simulation start time (and therefore zero
        # precip for first timestep)
        self.precip = ([0.0] * self.maxMA) + _conformed_rain[self.gage.Name]

        # Calculate temperatures. Only calculate temps from simulation start to end
        # once, after that reuse.
        global _common_temps
        if len(_common_temps) == 0:
            _common_temps = precalc_temps()
        self.temps = precalc_temps(self.maxMA) + _common_temps

        # Initialize values for first calculation timestep
        self.RWPrevF = self.RW0Fast
        self.RWPrevM = self.RW0Med
        self.RWPrevS = self.RW0Slow
        self.RPrevB = 0.0
        self.QPrevF = 0.0
        self.QPrevM = 0.0
        self.QPrevS = 0.0
        self.QPrevB = 0.0

        self.curIndex = 0
        self.curavgIndex = self.maxMA
        self.previousPrecips = self.precip[0 : self.maxMA + 1]
        self.previousTemps = self.temps[0 : self.maxMA + 1]

        # Run simulation for this subcatchment
        for t in _all_t:
            self.AMM_timestep(t)

    def calc_decay_constant(self, HL):
        if HL == 0:
            # Prevent divide by zero errors for unused components
            return 0.99
        else:
            return 0.5 ** (_calc_step_sec / HL)

    def AMM_timestep(self, t):
        # tempValue at current timestep t represents temp right at time t
        tempValue = self.temps[self.curavgIndex]
        self.previousTemps.append(tempValue)

        # Assume "end-of-interval" convention for precipitation, that is, that
        # precipValue at current timestep t represents rain volume on (t-1,t].
        precipValue = self.precip[self.curavgIndex]
        self.previousPrecips.append(precipValue)
        if precipValue > 0:
            pass

        # Take moving averages of rain and temperature
        MAs = {}
        for var in [
            "TPFast",
            "TPMed",
            "TPSlow",
            "TPBase",
            "MATFast",
            "MATMed",
            "MATSlow",
        ]:
            MAs[var] = self.MA(self.previousPrecips, getattr(self, var))

        for var in ["SATFast", "SATMed", "SATSlow", "SATBase"]:
            MAs[var] = self.MA(self.previousTemps, getattr(self, var))

        # SHCF (Level 3 for AMM, Level 2 for Base)
        if t.Month < 7 or (t.Month == 7 and t.Day <= 15):
            ColdSHCFFast = self.SpringColdSHCFFast
            ColdSHCFMed = self.SpringColdSHCFMed
            ColdSHCFSlow = self.SpringColdSHCFSlow
            ColdRBase = self.SpringColdRBase
        else:
            ColdSHCFFast = self.FallColdSHCFFast
            ColdSHCFMed = self.FallColdSHCFMed
            ColdSHCFSlow = self.FallColdSHCFSlow
            ColdRBase = self.FallColdRBase

        LFast = 1.2 * (ColdSHCFFast - self.HotSHCFFast)
        LMed = 1.2 * (ColdSHCFMed - self.HotSHCFMed)
        LSlow = 1.2 * (ColdSHCFSlow - self.HotSHCFSlow)
        LBase = 1.2 * (ColdRBase - self.HotRBase)

        # Do not allow SHCFt to drop below zero although this is possible at high
        # temperatures for very low values of Hot SHCF
        SHCFtFast = max(
            LFast / (1 + math.exp(-1 * self.k * (MAs["SATFast"] - self.x0)))
            + ColdSHCFFast
            - (11.0 / 12.0) * LFast,
            0,
        )
        SHCFtMed = max(
            LMed / (1 + math.exp(-1 * self.k * (MAs["SATMed"] - self.x0)))
            + ColdSHCFMed
            - (11.0 / 12.0) * LMed,
            0,
        )
        SHCFtSlow = max(
            LSlow / (1 + math.exp(-1 * self.k * (MAs["SATSlow"] - self.x0)))
            + ColdSHCFSlow
            - (11.0 / 12.0) * LSlow,
            0,
        )
        RtBase = max(
            LBase / (1 + math.exp(-1 * self.k * (MAs["SATBase"] - self.x0)))
            + ColdRBase
            - (11.0 / 12.0) * LBase,
            0,
        )

        # RW (Level 2 for AMM)
        RWtFast = (self.AMRFFast - 1) / math.log(
            self.AMRFFast
        ) * self.RDFast * SHCFtFast * MAs["MATFast"] + self.AMRFFast * self.RWPrevF
        RWtMed = (self.AMRFMed - 1) / math.log(
            self.AMRFMed
        ) * self.RDMed * SHCFtMed * MAs["MATMed"] + self.AMRFMed * self.RWPrevM
        RWtSlow = (self.AMRFSlow - 1) / math.log(
            self.AMRFSlow
        ) * self.RDSlow * SHCFtSlow * MAs["MATSlow"] + self.AMRFSlow * self.RWPrevS

        # Q (Level 1)
        QFast = (
            self.area
            * (1 - self.SFFast)
            / _calc_step_sec
            * (self.RDFast + (RWtFast + self.RWPrevF) / 2)
            * MAs["TPFast"]
            + self.SFFast * self.QPrevF
        )
        QMed = (
            self.area
            * (1 - self.SFMed)
            / _calc_step_sec
            * (self.RDMed + (RWtMed + self.RWPrevM) / 2)
            * MAs["TPMed"]
            + self.SFMed * self.QPrevM
        )
        QSlow = (
            self.area
            * (1 - self.SFSlow)
            / _calc_step_sec
            * (self.RDSlow + (RWtSlow + self.RWPrevS) / 2)
            * MAs["TPSlow"]
            + self.SFSlow * self.QPrevS
        )
        QBase = (
            self.area
            * (1 - self.SFBase)
            / _calc_step_sec
            * (RtBase + self.RPrevB)
            / 2
            * MAs["TPBase"]
            + self.SFBase * self.QPrevB
        )

        # Set values for next iteration
        self.RWPrevF = RWtFast
        self.RWPrevM = RWtMed
        self.RWPrevS = RWtSlow
        self.RWPrevB = RtBase
        self.QPrevF = QFast
        self.QPrevM = QMed
        self.QPrevS = QSlow
        self.QPrevB = QBase

        # Total
        FlowSum = QFast + QMed + QSlow + QBase

        # Calculate total Percent Capture from RD and RW
        PCFast = (self.RDFast + RWtFast) * 100  # To %
        PCMed = (self.RDMed + RWtMed) * 100  # To %
        PCSlow = (self.RDSlow + RWtSlow) * 100  # To %
        PCBase = RtBase * 100  # To %

        # Convert units
        QFast /= _Q_conv_factor
        QMed /= _Q_conv_factor
        QSlow /= _Q_conv_factor
        QBase /= _Q_conv_factor
        FlowSum /= _Q_conv_factor
        SHCFtFast /= _SHCF_conv_factor
        SHCFtMed /= _SHCF_conv_factor
        SHCFtSlow /= _SHCF_conv_factor
        precipValue /= _rain_conv_factor

        # Save results - not as elegant as it could be, but faster than alternatives
        self.results["Runoff_Total"][self.curIndex] = FlowSum
        if _full_tsb_detail is True:
            self.results["Runoff_Fast"][self.curIndex] = QFast
            self.results["Runoff_Med"][self.curIndex] = QMed
            self.results["Runoff_Slow"][self.curIndex] = QSlow
            self.results["Runoff_Base"][self.curIndex] = QBase
            self.results["PC_Fast"][self.curIndex] = PCFast
            self.results["PC_Med"][self.curIndex] = PCMed
            self.results["PC_Slow"][self.curIndex] = PCSlow
            self.results["PC_Base"][self.curIndex] = PCBase
            self.results["SHCF_Fast"][self.curIndex] = SHCFtFast
            self.results["SHCF_Med"][self.curIndex] = SHCFtMed
            self.results["SHCF_Slow"][self.curIndex] = SHCFtSlow
            self.results["Rain"][self.curIndex] = precipValue
            self.results["Temps"][self.curIndex] = tempValue

        # Set indices for next iteration
        self.curIndex += 1
        self.curavgIndex += 1

    def MA(self, previousData, ma_lag):
        # In the case that a parameter does not come out to a whole number of timesteps
        # account for the partial steps as well.
        real_steps = (
            ma_lag + 1
        )  # +1 because an averaging time of zero equates to one value to average
        whole_steps = int(math.floor(real_steps))
        part_steps = real_steps - whole_steps
        MA = sum(previousData[-whole_steps:]) / real_steps
        MA += previousData[-(whole_steps + 1)] * part_steps / real_steps
        return MA

    def twin_results(self, twin_results, twin_area):
        area_ratio = self.area / twin_area
        twin_results_copy = self.dict_deepish_copy(twin_results)
        twin_results_copy["Runoff_Total"] = [
            q * area_ratio for q in twin_results_copy["Runoff_Total"]
        ]
        if _full_tsb_detail == True:
            twin_results_copy["Runoff_Fast"] = [
                q * area_ratio for q in twin_results_copy["Runoff_Fast"]
            ]
            twin_results_copy["Runoff_Med"] = [
                q * area_ratio for q in twin_results_copy["Runoff_Med"]
            ]
            twin_results_copy["Runoff_Slow"] = [
                q * area_ratio for q in twin_results_copy["Runoff_Slow"]
            ]
            twin_results_copy["Runoff_Base"] = [
                q * area_ratio for q in twin_results_copy["Runoff_Base"]
            ]
        self.results = twin_results_copy

    def dict_deepish_copy(self, results):
        # Goes one layer deeper than shallow copy but 2 OOM faster than deepcopy
        new_results = {}
        for key in results.keys():
            new_results[key] = copy.copy(results[key])
        return new_results


class AMMRun:
    def __init__(self):
        self.model_name = os.path.basename(pcpy.SWMM.FilePath[0:-4])
        dir_name = pcpy.SWMM.FilePath[0:-4] + "_files"
        if os.path.isdir(dir_name) == False:
            os.mkdir(dir_name)
        self.layer_fname = dir_name + "\AMM_Subcatchments.shp"
        self.inflow_fname = dir_name + "\AMM_Subcatchments_Inflow.txt"
        self.tsb_fname = dir_name + "\AMM_Subcatchments.tsb"
        self.amm_layer = None  # If cannot be set up by enable_amm method, stop routing

    def enable_amm(self):
        # Check that the AMM_Subcatchments.shp file exists and that it is loaded.
        # Otherwise offer to help the user.
        # Does not check the .shp file has the appropriate attributes.
        layer_fname = self.layer_fname
        if not os.path.isfile(layer_fname):
            dlg = pcpy.show_messagebox(
                (
                    'The "AMM_Subcatchments.shp" file cannot be found in the "%s_files" directory.\n'
                    "This is normal if this is the first time you are running this script.\n"
                    "Otherwise you may have forgotten to copy the shapefile from a previous scenario.\n\n"
                    'Would you like to create a new "AMM_Subcatchments.shp" file?'
                )
                % self.model_name,
                "",
                pcpy.Enum.IconType.Question,
                pcpy.Enum.ButtonType.YesNo,
            )
            if dlg == pcpy.Enum.DlgResult.No:
                return None
            elif dlg == pcpy.Enum.DlgResult.Yes:
                pcpy.Map.add_layer(layer_fname, "polygon")
                self.amm_layer = self.get_loaded_layer(layer_fname)
                self.add_amm_attributes(self.amm_layer)
                return None

        self.amm_layer = self.get_loaded_layer(layer_fname)
        if self.amm_layer is None:
            dlg = pcpy.show_messagebox(
                (
                    'An "AMM_Subcatchments.shp" file exists in the "%s_files" directory, '
                    "but it is not open in the current model.\n"
                    "This could be perfectly innocent, "
                    "or it could indicate you have the wrong AMM_Subcatchments open.\n\n"
                    "(If this is a new scenario did you forget to close the old AMM_Subcatchments layer?\n"
                    "When saving as a new scenario best practice is to close the old layer, copy the shapefile over, and reopen the new layer.)\n\n\n"
                    'Would you like to load the "AMM_Subcatchments.shp" file and proceed with the calculation?'
                )
                % self.model_name,
                "",
                pcpy.Enum.IconType.Question,
                pcpy.Enum.ButtonType.YesNo,
            )
            if dlg == pcpy.Enum.DlgResult.No:
                return None
            elif dlg == pcpy.Enum.DlgResult.Yes:
                pcpy.Map.open_layer(layer_fname)
                self.amm_layer = self.get_loaded_layer(layer_fname)

    def add_amm_attributes(self, amm_layer):
        self.amm_layer.Locked = False
        area_unit = {"METRIC": "ha", "IMPERIAL": "ac"}[_unit_system]
        SHCF_unit = {"METRIC": "1/mm", "IMPERIAL": "1/in"}[_unit_system]

        self.add_user_attribute(
            "Name",
            "Name",
            "User-assigned name of subcatchment",
            "",
            "Text",
            "1. Attributes",
        )
        self.add_user_attribute(
            "Descript",
            "Description",
            "Optional comment or description.",
            "",
            "Text",
            "1. Attributes",
        )
        self.add_user_attribute(
            "Tag",
            "Tag",
            "Optional category or classification.",
            "",
            "Text",
            "1. Attributes",
        )
        self.add_user_attribute(
            "Outlet",
            "Outlet",
            "Name of node that receives runoff",
            "",
            "Text",
            "1. Attributes",
        )
        self.add_user_attribute(
            "ScaleArea",
            "Use Scaled Area?",
            "If set to True the area of the subcatchment is automatically updated from the scaled polygon area at runtime.",
            "",
            "Boolean",
            "1. Attributes",
        )
        self.add_user_attribute(
            "Area",
            "Area",
            "Area of subcatchment.",
            area_unit,
            "Number",
            "1. Attributes",
        )
        self.add_user_attribute(
            "RainGage",
            "Rain Gage",
            "Name of rain gage assigned to subcatchment.",
            "",
            "Text",
            "1. Attributes",
        )
        self.add_user_attribute(
            "MeterBasin",
            "Meter Basin",
            "Optional name of the basin or meter basin of which this subcatchment is a part. For user reference; not used in calculation.",
            "",
            "Text",
            "1. Attributes",
        )

        self.add_user_attribute(
            "HotTemp",
            "Hot Temp",
            "Hot reference temperature.",
            "degrees",
            cat="2. Shared",
        )
        self.add_user_attribute(
            "ColdTemp",
            "Cold Temp",
            "Cold reference temperature",
            "degrees",
            cat="2. Shared",
        )

        self.add_user_attribute(
            "RDFast",
            "Fast RD",
            "Dry-Weather percent capture of the Fast component.",
            "%",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "RDMed",
            "Medium RD",
            "Dry-Weather percent capture of the Medium component.",
            "%",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "RDSlow",
            "Slow RD",
            "Dry-Weather percent capture of the Slow component.",
            "%",
            cat="5. Slow",
        )
        self.add_user_attribute(
            "TPFast",
            "Fast TP",
            "Time to peak of the Fast component.",
            "hr",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "TPMed",
            "Medium TP",
            "Time to peak of the Medium component.",
            "hr",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "TPSlow",
            "Slow TP",
            "Time to peak of the Slow component.",
            "hr",
            cat="5. Slow",
        )
        self.add_user_attribute(
            "TPBase",
            "Base TP",
            "Time to peak of the Base component.",
            "hr",
            cat="6. Base",
        )
        self.add_user_attribute(
            "HHLFast",
            "Fast HHL",
            "Hydrograph half life of the Fast component.",
            "hr",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "HHLMed",
            "Medium HHL",
            "Hydrograph half life of the Medium component.",
            "hr",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "HHLSlow",
            "Slow HHL",
            "Hydrograph half life of the Slow component.",
            "hr",
            cat="5. Slow",
        )
        self.add_user_attribute(
            "HHLBase",
            "Base HHL",
            "Hydrograph half life of the Base component.",
            "hr",
            cat="6. Base",
        )

        self.add_user_attribute(
            "AMHLFast",
            "Fast AMHL",
            "Fast Antecedent Moisture Half-Life.",
            "days",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "AMHLMed",
            "Medium AMHL",
            "Medium Antecedent Moisture Half-Life.",
            "days",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "AMHLSlow",
            "Slow AMHL",
            "Slow Antecedent Moisture Half-Life.",
            "days",
            cat="5. Slow",
        )

        self.add_user_attribute(
            "HtSHCFFast",
            "Fast Hot SHCF",
            "Hot Seasonal Hydrologic Condition Factor for the Fast component.",
            SHCF_unit,
            cat="3. Fast",
        )
        self.add_user_attribute(
            "HtSHCFMed",
            "Medium Hot SHCF",
            "Hot Seasonal Hydrologic Condition Factor for the Medium component.",
            SHCF_unit,
            cat="4. Medium",
        )
        self.add_user_attribute(
            "HtSHCFSlow",
            "Slow Hot SHCF",
            "Hot Seasonal Hydrologic Condition Factor for the Slow component.",
            SHCF_unit,
            cat="5. Slow",
        )
        self.add_user_attribute(
            "SpClSHCFF",
            "Fast Spring Cold SHCF",
            "Cold Seasonal Hydrologic Condition Factor from Jan. 1 to July 15 for the Fast component.",
            SHCF_unit,
            cat="3. Fast",
        )
        self.add_user_attribute(
            "SpClSHCFM",
            "Medium Spring Cold SHCF",
            "Cold Seasonal Hydrologic Condition Factor from Jan. 1 to July 15 for the Medium component.",
            SHCF_unit,
            cat="4. Medium",
        )
        self.add_user_attribute(
            "SpClSHCFS",
            "Slow Spring Cold SHCF",
            "Cold Seasonal Hydrologic Condition Factor from Jan. 1 to July 15 for the Slow component.",
            SHCF_unit,
            cat="5. Slow",
        )
        self.add_user_attribute(
            "FlClSHCFF",
            "Fast Fall Cold SHCF",
            "Cold Seasonal Hydrologic Condition Factor from July 15 to Dec. 31. for the Fast component",
            SHCF_unit,
            cat="3. Fast",
        )
        self.add_user_attribute(
            "FlClSHCFM",
            "Medium Fall Cold SHCF",
            "Cold Seasonal Hydrologic Condition Factor from July 15 to Dec. 31. for the Medium component",
            SHCF_unit,
            cat="4. Medium",
        )
        self.add_user_attribute(
            "FlClSHCFS",
            "Slow Fall Cold SHCF",
            "Cold Seasonal Hydrologic Condition Factor from July 15 to Dec. 31. for the Slow component",
            SHCF_unit,
            cat="5. Slow",
        )

        self.add_user_attribute(
            "HtRBase",
            "Base Hot R",
            "Percent capture during Hot conditions for the Base component.",
            "%",
            cat="6. Base",
        )
        self.add_user_attribute(
            "SpClRB",
            "Base Spring Cold R",
            "Percent Capture during Cold conditions for the Base component from Jan. 1 to July 15.",
            "%",
            cat="6. Base",
        )
        self.add_user_attribute(
            "FlClRB",
            "Base Fall Cold R",
            "Percent Capture during Cold conditions for the Base component from July 15 to Dec. 31.",
            "%",
            cat="6. Base",
        )

        self.add_user_attribute(
            "MATFast",
            "Fast MAT",
            "Moisture Averaging Time for the Fast component.",
            "days",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "MATMed",
            "Medium MAT",
            "Moisture Averaging Time for the Medium component.",
            "days",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "MATSlow",
            "Slow MAT",
            "Moisture Averaging Time for the Slow component.",
            "days",
            cat="5. Slow",
        )
        self.add_user_attribute(
            "SATFast",
            "Fast SAT",
            "Seasonal Averaging Time for the Fast component.",
            "days",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "SATMed",
            "Medium SAT",
            "Seasonal Averaging Time for the Medium component.",
            "days",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "SATSlow",
            "Slow SAT",
            "Seasonal Averaging Time for the Slow component.",
            "days",
            cat="5. Slow",
        )
        self.add_user_attribute(
            "SATBase",
            "Base SAT",
            "Seasonal Averaging Time for the Base component.",
            "days",
            cat="6. Base",
        )

        self.add_user_attribute(
            "RW0Fast",
            "Fast Initial RW",
            "RW (wet percent capture) at start of simulation for Fast component.",
            "unitless",
            cat="3. Fast",
        )
        self.add_user_attribute(
            "RW0Med",
            "Medium Initial RW",
            "RW (wet percent capture) at start of simulation for Medium component.",
            "unitless",
            cat="4. Medium",
        )
        self.add_user_attribute(
            "RW0Slow",
            "Slow Initial RW",
            "RW (wet percent capture) at start of simulation for Slow component.",
            "unitless",
            cat="5. Slow",
        )

    def get_loaded_layer(self, layer_fname):
        for layer in pcpy.Map.Layers:
            if layer.FilePath == layer_fname:
                return layer
        return None

    def add_user_attribute(
        self, attr_name, alias_name, desc, unit, data_type="Number", cat="Attributes"
    ):
        attr_name = attr_name.upper()
        if attr_name in self.amm_layer.Attributes:
            return
        attr = pcpy.Attribute(attr_name, data_type)  # Data type could be Text or Number
        attr.UserFriendlyName = (
            alias_name if unit == "" else "%s (%s)" % (alias_name, unit)
        )
        attr.Description = desc
        attr.Category = cat
        self.amm_layer.add_attribute(attr)

    def routing(self):
        # Check inflows file settings and warn user if needed
        files = list(_options.InterfaceFiles)
        amm_files = [f.File[-28:] == "AMM_Subcatchments_Inflow.txt" for f in files]
        non_amm_files = [i for (i, v) in zip(files, amm_files) if not v]
        non_amm_inflows_files = [f.Type == "INFLOWS" for f in non_amm_files]
        if any(non_amm_inflows_files):
            dlg = pcpy.show_messagebox(
                (
                    "This script saves its results to an INFLOWS file for use by the SWMM Engine. "
                    "The SWMM Engine can only use one INFLOWS file in a simulation.\n"
                    "Additional INFLOWS files are ignored.\n\n"
                    "It appears that an INFLOWS file is already associated with this model.\n\n"
                    "Before running the simulation you should either delete an old INFLOWS file or manually combine the INFLOWS files.\n"
                    "(Make sure the combined files does not have multiple inflow values at the same node at the same time.)\n\n"
                    'INFLOWS file settings are available in the "Simulation Options" menu.'
                ),
                "USE INFLOWS file already in use",
                pcpy.Enum.IconType.Important,
                pcpy.Enum.ButtonType.OK,
            )

        # Skip calculation if there is no AMM_Subcatchments layer or no items in the layer
        if self.amm_layer is None:
            return
        amm_entities = self.amm_layer.get_entities()
        if len(amm_entities) == 0:
            return

        # Initialize times
        global _start_t, _end_t, _all_t, _all_t_pydatetime
        _start_t = get_datetime(_options.StartDate, _options.StartTime)
        _end_t = get_datetime(_options.EndDate, _options.EndTime)
        t = _start_t
        while t <= _end_t:
            _all_t.append(t)  # List of .NET DateTime
            t = t.AddMinutes(_calc_step_min)
        _all_t_pydatetime = [
            datetime.datetime(dt) for dt in _all_t
        ]  # List of Python datetime.datetime

        # Initialize each AMM subcatchment
        amm_subs = [AMMSub(entity) for entity in amm_entities]

        # Run calcs subcatchment by subcatchment
        i = 0.0
        for sub in amm_subs:
            # Recreating the progress bar each time because something is closing it
            bar1 = pcpy.ProgressBar(
                "Calculating AMM Subcatchments (%i%s)" % (i / len(amm_subs) * 100, "%"),
                len(amm_subs),
            )
            bar1.update(i)
            if sub.all_params in _already_calced_subs.keys():
                # If a twin catchment has already been calculated we can take a big
                # shortcut and twin flows
                twin_sub = _already_calced_subs[sub.all_params]
                sub.twin_results(twin_sub.results, twin_sub.area)
            else:
                # Otherwise run full calcs and save for use as possible future twin
                sub.AMM_run()
                _already_calced_subs[sub.all_params] = sub
            i += 1

        # Generate inflow interface file
        bar2 = pcpy.ProgressBar("Exporting Results to SWMM", len(_all_t))
        inflow_data = defaultdict(float)  # key = sub outlet name
        unique_outlets = {sub.outlet for sub in amm_subs}  # Create a set
        with open(self.inflow_fname, "wt") as f:
            f.write("%s\n" % "SWMM5 Interface File")
            f.write("%s\n" % "Inflow created for AMM subcatchments.")
            f.write("%d  - reporting time step in sec\n" % (_calc_step_min * 60))
            f.write("%s\n" % "1    - number of constituents as listed below:")
            f.write("FLOW %s\n" % _flow_unit)
            f.write("%d    - number of nodes as listed below:\n" % len(unique_outlets))
            for outlet in unique_outlets:
                f.write("%s\n" % outlet)
            f.write("%s\n" % "Node             Year Mon Day Hr  Min Sec FLOW")

            for i in range(len(_all_t)):
                t = _all_t[i]
                time_string = "%-5s%-4s%-4s%-4s%-4s%-4s" % (
                    t.Year,
                    t.Month,
                    t.Day,
                    t.Hour,
                    t.Minute,
                    t.Second,
                )
                inflow_data.clear()
                for sub in amm_subs:
                    inflow_data[sub.outlet] += sub.results["Runoff_Total"][i]
                for outlet in unique_outlets:
                    f.write(
                        "%-16s " % outlet + time_string + "%g\n" % inflow_data[outlet]
                    )
                bar2.update()

        # Set model inflow interface file
        # Intentionally excludes any old AMM files from old scenarios
        non_amm_files.append(pcpy.InterfaceFile("Use", "INFLOWS", self.inflow_fname))
        _options.InterfaceFiles = files

        # Write to the tsb file
        tsb_f, tsb_funcs = self.get_tsb_funcs()
        k = 0
        for sub in amm_subs:
            for meas_name in _meas_names.keys():
                func_index = _meas_names[meas_name][0]
                loc_name = sub.name
                if _meas_names[meas_name][1] == True:
                    loc_name += "_" + meas_name
                bar3 = pcpy.ProgressBar(
                    "Saving Results to TSB", len(amm_subs) * len(_meas_names)
                )
                bar3.update(k)
                loc = tsb_funcs[func_index].add_location(loc_name)
                loc.Data = tuple(
                    pcpy.DateTimeValue(_all_t[j], sub.results[meas_name][j])
                    for j in range(len(_all_t))
                )
                k += 1
            bar3.update()
        tsb_f.save()
        self.amm_layer.refresh_timeseries()

    def get_tsb_funcs(self):
        for f in pcpy.Graph.Files:
            if f.FilePath == self.tsb_fname:
                tsb_f = f
                break
        else:
            tsb_f = pcpy.Graph.add_file(self.tsb_fname)

        for func in tsb_f.Functions:
            tsb_f.delete_function(func.Name, func.Units, func.Category)

        tsb_flow_unit = {
            "CMS": "m3/s",
            "LPS": "L/s",
            "MLD": "ML/d",
            "CFS": "cfs",
            "GPM": "gpm",
            "MGD": "mgd",
        }[_flow_unit]
        tsb_SHCF_unit = {"IMPERIAL": "1/in", "METRIC": "1/mm"}[_unit_system]
        tsb_rain_unit = {"IMPERIAL": "in", "METRIC": "mm"}[_unit_system]

        tsb_funcs = [
            tsb_f.add_function("Runoff", tsb_flow_unit, "AMM Subcatchments"),
        ]
        if _full_tsb_detail == True:
            tsb_funcs += [
                tsb_f.add_function("Percent Capture", "%", "AMM Subcatchments"),
                tsb_f.add_function("SHCF", tsb_SHCF_unit, "AMM Subcatchments"),
                tsb_f.add_function("Rain", tsb_rain_unit, "AMM Subcatchments"),
                tsb_f.add_function("Temperature", "degrees", "AMM Subcatchments"),
            ]

        return tsb_f, tsb_funcs


def precalc_temps(maxMA=None):
    # Return list of temps on [s_time, e_time] (bounds inclusive)
    if maxMA is None:  # For common_temps
        out_times = _all_t_pydatetime
        check_ordered = True
    else:  # Subsequent calls, where maxMA is an int
        s_time = datetime.datetime(_start_t) - datetime.timedelta(
            minutes=maxMA * _calc_step_min
        )
        out_times = [  # len(out_times) = maxMA
            s_time + datetime.timedelta(minutes=(st * _calc_step_min))
            for st in range(maxMA)
        ]
        check_ordered = False  # Don't need to repeat this check every time through

    if _use_temp_timeseries == True:
        temp_ts = load_and_validate_ts(
            _temp_timeseries, expected_overlap="full", check_ordered=check_ordered
        )
        temp_list = []
        for dtv in temp_ts.Data:
            temp_list.append((datetime.datetime(dtv.DateTime), dtv.Value))
        final_temps = conform_ts(temp_list, out_times)
    else:
        final_temps = [interp_seasonal_temp(t) for t in out_times]

    return final_temps


def conform_rainfall(gage):
    """Conform rainfall data to a list of incremental values in depth units of meters at\
         same time step as the calc step"""

    precip_ts = load_and_validate_ts(gage.Series)

    precip_step_min = get_time(gage.TimeInterval)
    cum_rain = 0.0
    cum_precip_list = []
    # Convert rain data to Cumulative format
    if gage.RainFormat == "CUMULATIVE":
        # Assumes that for 'Cumulative' data the reported value is the instantaneous
        # cumulative total at time t.
        for dtv in precip_ts.Data:
            cum_rain = dtv.Value * _rain_conv_factor  # to meters
            dt = datetime.datetime(dtv.DateTime)
            cum_precip_list.append((dt, cum_rain))
    elif gage.RainFormat == "INTENSITY":
        # Assumes "start-of-interval" convention that for 'Intensity' data the rain at
        # timestep t represents rain on [t,t+1)
        # This is consistent with EPA SWMM
        # Assumes the rain gage time step is consistently used, but intermittent values
        # timesteps may be missing (e.g. zeros removed)
        # Assumes intensity is in mm/hr or in./hr units
        dt = datetime.datetime(precip_ts.Data[0].DateTime)
        cum_precip_list.append((dt, cum_rain))
        for dtv in precip_ts.Data:
            dt = datetime.datetime(dtv.DateTime) + datetime.timedelta(
                minutes=precip_step_min
            )
            cum_rain += (
                dtv.Value * precip_step_min / 60 * _rain_conv_factor
            )  # to meters
            cum_precip_list.append((dt, cum_rain))
        dt = datetime.datetime(dtv.DateTime) + datetime.timedelta(
            minutes=precip_step_min
        )
        cum_precip_list.append((dt, cum_rain))
    elif gage.RainFormat == "VOLUME":
        # Assumes "start-of-interval" convention that for 'Volume' data the rain at
        # timestep t represents rain on [t,t+1)
        # This is consistent with EPA SWMM
        # Assumes the rain gage time step is consistently used, but intermittent values
        # timesteps may be missing (e.g. zeros removed)
        dt = datetime.datetime(precip_ts.Data[0].DateTime)
        cum_precip_list.append((dt, cum_rain))
        for dtv in precip_ts.Data:
            dt = datetime.datetime(dtv.DateTime) + datetime.timedelta(
                minutes=precip_step_min
            )
            cum_rain += dtv.Value * _rain_conv_factor  # to meters
            cum_precip_list.append((dt, cum_rain))

    out_times = [
        _all_t_pydatetime[0] - datetime.timedelta(minutes=_calc_step_min)
    ] + _all_t_pydatetime
    # add one more timestep because we'll eventually lose one converting from cumulative
    # to incremental

    norm_precip = conform_ts(cum_precip_list, out_times)

    # Convert from cumulative to incremental (volume)
    # Uses "end-of-interval" convention - each timestep t represents rain falling on (t-1,t]
    inc_precip = []
    a = norm_precip[0]
    for b in norm_precip[1:]:
        # Setting min. value to zero prevents negative flows if original time series
        # ends before simulation end
        inc_precip.append(max(b - a, 0))
        a = b

    return inc_precip


def load_and_validate_ts(ts_name, expected_overlap="partial", check_ordered=True):
    # expected_overlap should be "partial" or "full" and defines test to trigger error
    ts = pcpy.SWMM.TimeSeries[ts_name]
    if len(ts.Data) < 3:
        # Test
        raise Exception(
            'Time Series "%s": this script currently does not support external data files, only user input time series data.'
            % ts_name
        )

    # Test that the timeseries partially or fully overlaps the simulation period
    ts_start = ts.Data[0].DateTime
    ts_end = ts.Data[-1].DateTime
    if expected_overlap == "partial":
        try:
            assert not _start_t > ts_end
            assert not _end_t < ts_start
        except AssertionError:
            raise Exception(
                'Data for time series "%s" does not overlap the simulation period. This doesn\'t seem right...'
                % ts_name
            )
    elif expected_overlap == "full":
        try:
            assert ts_start <= _start_t
            assert ts_end >= _end_t
        except AssertionError:
            raise Exception(
                'Data for temperature time series "%s" does not fully overlap the simulation period. This is required for temperature time series.'
                % ts_name
            )

    # Data should be ordered or bad things might happen
    if check_ordered is True:
        old_dt = ts.Data[0].DateTime
        try:
            for dtv in ts.Data[1:]:
                dt = dtv.DateTime
                assert dt > old_dt
                old_dt = dt
        except AssertionError:
            raise Exception(
                'Data appears to be out of order for time series "%s". Data should be ordered or bad things might happen.'
                % ts_name
            )

    return ts


def conform_ts(ts, out_times):
    """Takes an ordered list of PyDateTimeValues of arbitrary (and possibly uneven)
    interval and a list of datetime.datetimes of arbitary (and possibly uneven) interval.

    ts should be a list of tuples of length 2 of types (datetime.datetime, integer or float)
    out_times should be a list of type datetime.datetime

    Outputs a list of values conformed to out_times using linear interpolation where necessary.
    """
    conf_ts = []
    for dt in out_times:
        while len(ts) >= 2:
            dtv0 = ts[0]
            dtv1 = ts[1]
            if dtv1[0] <= dt:
                ts.pop(0)
                continue
            elif dtv0[0] == dt:
                b = dtv0[1]
                conf_ts.append(b)
                break
            elif dtv0[0] < dt and dtv1[0] > dt:
                b = lin_interp(dt, dtv0[0], dtv1[0], dtv0[1], dtv1[1])
                conf_ts.append(b)
                break
            elif dtv0[0] > dt:
                conf_ts.append(0)
                break
        if len(ts) == 1:
            dtv0 = ts[0]
            b = dtv0[1]
            conf_ts.append(b)
            ts.pop(0)
        elif len(ts) == 0:
            conf_ts.append(0)
    return conf_ts


def get_time(time_s):
    times = [float(s) for s in time_s.split(":")]
    if len(times) == 2:
        hr, min = times
        time_min = hr * 60 + min
    else:
        hr, min, sec = times
        time_min = hr * 60 + min + sec / 60
    return time_min


def get_datetime(date_s, time_s):
    mon, day, yr = [float(s) for s in re.split("-|/", date_s)]
    hr, min, sec = 0, 0, 0
    lt_time = re.split(":", time_s)
    if len(lt_time) == 3:
        hr, min, sec = [float(s) for s in lt_time]
    return pcpy.DateTime(yr, mon, day, hr, min, sec)


def lin_interp(t, t0, t1, y0, y1):
    # Assumes t, t0, and t1 are python datetime.datetime objects
    m = (y1 - y0) / (t1 - t0).total_seconds()
    y = y0 + m * (t - t0).total_seconds()
    return y


def interp_seasonal_temp(t):
    month = t.month
    day = t.day
    year = t.year
    leap = 1 if year % 4 == 0 else 0
    DaysInMonth = {
        1: 30.0,
        2: 28.0 + leap,
        3: 31.0,
        4: 30.0,
        5: 31.0,
        6: 30.0,
        7: 31.0,
        8: 31.0,
        9: 30.0,
        10: 31.0,
        11: 30.0,
        12: 31.0,
    }

    startMonthKey = month
    endMonthKey = month
    middleDay = math.ceil(DaysInMonth[month] / 2)
    if day < middleDay:
        startMonthKey = month - 1 if month != 1 else 12
    else:
        endMonthKey = month + 1 if month != 12 else 1
    totalDays = math.floor(DaysInMonth[startMonthKey] / 2) + math.ceil(
        DaysInMonth[endMonthKey] / 2
    )
    daysBetween = (
        day - math.ceil(DaysInMonth[month] / 2)
        if startMonthKey == month
        else day + math.floor(DaysInMonth[startMonthKey] / 2)
    )
    percentVal = float(daysBetween) / float(totalDays)
    tempreturn = (
        percentVal * _tempDict[endMonthKey]
        + (1 - percentVal) * _tempDict[startMonthKey]
    )
    return tempreturn


# Main
if __name__ == "<module>":
    if _calc_step_min == 0:
        _calc_step_min = get_time(_options.WetStep)
        if _calc_step_min == 0:
            raise Exception("Timestep cannot be zero.")
        _calc_step_sec = _calc_step_min * 60
    amm = AMMRun()
    amm.enable_amm()
    amm.routing()
    print("\nAMM Finished")
    if _run_hydraulics == True:
        pcpy.SWMM.run()


# = = = = =

# This script is licensed under the terms of the MIT license, reproduced below.

# Copyright (c) 2021-2022 RJN Group, Inc.

# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
# DEALINGS IN THE SOFTWARE.

# = = = = =
