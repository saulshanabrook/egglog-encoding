################################################################################
# run.py
# The entrypoint for running an experiment.
################################################################################

from modules.experiment import *

args = Args().parse()
experiment(args)
