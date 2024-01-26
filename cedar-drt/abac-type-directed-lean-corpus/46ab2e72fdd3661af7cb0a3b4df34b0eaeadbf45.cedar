permit(
  principal == a::"",
  action,
  resource is a in a::""
) when {
  ((true && ((if ((ip("54.54.62.54")).isIpv4()) then [[], []] else (if false then [] else [])) == (if (resource is a) then [[], [], []] else []))) && true) && false
};
