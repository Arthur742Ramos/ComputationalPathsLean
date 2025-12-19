# CI & Releases

Local CI mirror (from `computational_paths/`):

- Build: `.\lake.cmd build`
- Run exe: `.\lake.cmd exe computational_paths`
- Clean rebuild: `.\lake.cmd clean` then `.\lake.cmd build`

Version bump:
- Update `ComputationalPaths/Basic.lean` (`libraryVersion`)
- Build + run exe to confirm

Toolchain bump:
- Edit `lean-toolchain`
- Build; run `lake update` if dependencies need repinning; build again

