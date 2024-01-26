permit(
  principal in a::"vz6\0\0\0",
  action == Action::"action",
  resource == a::"vz6\0\0\0"
) when {
  ((true && (((if false then resource else resource) has "C") == ((if false then resource else resource) has "C"))) && ((if (resource has "C") then a::"vz6\0\0\0" else a::"vz6\0\0\0") has "C")) && ((if ((ip("182.182.182.182")).isLoopback()) then (-15702990074235210) else 201) == 0)
};
