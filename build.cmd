@echo off
rem Build mst.exe with the MSVC toolchain.  Run:  build.cmd
setlocal
call "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
if errorlevel 1 ( echo [build] vcvars64 failed & exit /b 1 )
cl /nologo /O2 /W4 /std:c11 /Fe:mst.exe mst.c
exit /b %errorlevel%
