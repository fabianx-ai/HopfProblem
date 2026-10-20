import glob,subprocess,sys
fail=0
for f in sorted(glob.glob("Lib/AlgebraicTopology/Hurewicz/*.lean")):
    old=subprocess.run(["git","show",f"f9a24ba:{f}"],capture_output=True,text=True).stdout
    new=open(f).read()
    m = new == old.replace("SecondHurewicz","Hurewicz.DegreeTwo")
    print(("MATCH" if m else "NOMATCH"),f)
    if not m: fail=1
print("RESULT:","ALL MATCH" if not fail else "MISMATCHES PRESENT")
sys.exit(fail)
