"""Runs the frozen coupled_stochastic/real_env.py with the data directory pointed at analysis/data
(the frozen script hard-codes the author's local path). The frozen file is not modified.
Usage: python run_real.py dev|confirm"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "coupled_stochastic"))
import real_env
real_env.DATA = os.environ.get("FRED_DATA", os.path.join(HERE, "data"))
real_env.main(sys.argv[1] if len(sys.argv) > 1 else "dev")
