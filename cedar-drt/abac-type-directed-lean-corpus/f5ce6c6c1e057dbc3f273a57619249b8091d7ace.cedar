@J("")
@z("3:\0\0\0")
permit(
  principal in a::"6",
  action in [Action::"action"],
  resource == a::"6"
) when {
  ((true && (if (if ((ip("110.109.119.186/9")).isMulticast()) then (!false) else ((ip("362d:3636:3636:3636:3636:3636:36c9:c9c9")).isIpv4())) then (resource has "mnm") else (if (principal is a) then ((ip("0.51.51.51")).isIpv4()) else (!true)))) && (!(!((ip("255.54.54.54/24")).isIpv4())))) && (!((if false then (ip("54.242.0.0")) else (ip("0.0.0.0"))).isIpv4()))
};
