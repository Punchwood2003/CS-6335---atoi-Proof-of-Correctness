@echo off
REM First-time setup script for atoi proofs
REM Initializes git submodules and builds Picinae source files

echo ========================================
echo First Time Setup for atoi Proofs
echo ========================================
echo.

REM Initialize and update git submodules (including Picinae)
echo Initializing git submodules...
git submodule update --init --recursive
if errorlevel 1 (
    echo Error initializing git submodules
    pause
    exit /b 1
)

REM Check if Picinae folder exists and has content
if not exist "Picinae\Picinae_core.v" (
    echo Error: Picinae submodule not found after initialization
    pause
    exit /b 1
)

echo Picinae submodule initialized successfully!

echo.
echo Copying updated Picinae files...
if exist "UpdatedPicinaeFiles" (
    xcopy /Y "%~dp0UpdatedPicinaeFiles\*.v" "%~dp0Picinae\"
    if errorlevel 1 (
        echo Warning: Could not copy some updated Picinae files
    ) else (
        echo Updated Picinae files copied successfully!
    )
) else (
    echo No UpdatedPicinaeFiles directory found, skipping file copy.
)

echo.
echo Building Picinae source files...
cd /d "%~dp0\Picinae"
call windows_build.bat
if errorlevel 1 (
    echo Error building Picinae source files
    cd /d "%~dp0"
    pause
    exit /b 1
)
cd /d "%~dp0"

echo.
echo ========================================
echo First-time setup completed successfully!
echo ========================================
echo You can now run windows_build.bat to build the atoi proofs.
