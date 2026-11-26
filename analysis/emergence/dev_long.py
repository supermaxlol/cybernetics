"""DEV only: does a larger search budget change class 1 (hidden actuator) and the mix? Usage: python dev_long.py SEED"""
import sys, time, json, emerge as E
E.LPC = 24; s = int(sys.argv[1]); out = {}
for nm, cls in (("c1", (1,)), ("mix", E.SETS["mix"])):
    if nm == "mix": E.LPC = 8
    for arm in ("emerge", "free", "full", "five"):
        for gens, P in ((80, 80), (400, 120)):
            t = time.time(); G = E.evolve(arm, cls, s, gens, P); m = E.measure(arm, G, cls, s); out[f"{nm}/{arm}/{gens}"] = m
            print(nm, arm, gens, {k: (round(v, 3) if isinstance(v, float) else v) for k, v in m.items()}, round(time.time() - t), "s", flush=True)
json.dump(out, open(f"dev_long_{s}.json", "w"), indent=1)
