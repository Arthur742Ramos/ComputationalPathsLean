[CmdletBinding()]
param(
    [switch]$Full
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$RepoRoot = Resolve-Path (Join-Path $ScriptDir "..")
Set-Location $RepoRoot

function Invoke-Check {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Label,

        [Parameter(Mandatory = $true)]
        [string]$FilePath,

        [string[]]$ArgumentList = @()
    )

    Write-Host ""
    Write-Host "==> $Label"
    & $FilePath @ArgumentList
    if ($LASTEXITCODE -ne 0) {
        throw "$Label failed with exit code $LASTEXITCODE."
    }
}

Invoke-Check "Checking diff whitespace" "git" @("diff", "--check")
Invoke-Check "Printing Lean version" "lake" @("-R", "--no-ansi", "env", "lean", "--version")
Invoke-Check "Building compact core module" "lake" @("--no-ansi", "build", "ComputationalPaths.Basic")

if ($Full) {
    Invoke-Check "Building full library" "lake" @("--no-ansi", "build")
} else {
    Write-Host ""
    Write-Host "Skipping full lake build by default. Run 'lake build' manually, or 'scripts\check.ps1 -Full', when you need full validation."
}
