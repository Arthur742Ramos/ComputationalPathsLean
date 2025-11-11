@echo off
setlocal
set "ELAN_LAKE=%USERPROFILE%\.elan\bin\lake.exe"
if exist "%ELAN_LAKE%" (
  "%ELAN_LAKE%" %*
) else (
  echo lake.exe not found in %USERPROFILE%\.elan\bin>&2
  exit /b 1
)
