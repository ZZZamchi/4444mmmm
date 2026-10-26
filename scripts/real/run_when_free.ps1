# Wait until enough physical memory is available, then run the G3 probe on one dataset with
# a single Lean worker. Usage: run_when_free.ps1 <dataset> [minMB]
param([string]$Dataset, [int]$MinMB = 4500)
$env:PYTHONIOENCODING = 'utf-8'
$env:LEAN_WORKERS = '1'
while ((Get-Counter '\Memory\Available MBytes').CounterSamples.CookedValue -lt $MinMB) {
    Start-Sleep -Seconds 60
}
"start $(Get-Date -Format s) available=$((Get-Counter '\Memory\Available MBytes').CounterSamples.CookedValue)MB"
python scripts/real/g3_probe.py anthropic/claude-opus-5.5 $Dataset
