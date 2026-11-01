@echo off
setlocal

if /I not "%~1"=="fast" if /I not "%~1"=="full" (
    echo Usage: %~nx0 fast^|full
    exit /b 1
)

set MODE=%~1
set DYNAHINTS_BENCH_MODE=%MODE%

IF EXIST "target\criterion" (
    echo Clearing previous criterion benchmark cache...
    RMDIR /S /Q "target\criterion"
)

echo ========================================
echo       Step 1: Running cargo bench
echo       Mode: %MODE%
echo ========================================
cargo bench --bench synthetic_prove
if %ERRORLEVEL% NEQ 0 (
    echo Cargo bench failed!
    exit /b %ERRORLEVEL%
)

echo.
echo ========================================
echo  Step 2: Generating benchmark results
echo ========================================
python generate-table.py %MODE%
if %ERRORLEVEL% NEQ 0 (
    echo Python script failed!
    exit /b %ERRORLEVEL%
)

echo.
echo Done! The results are saved in benchmark_results.md
pause
