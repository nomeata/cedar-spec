forbid(
  principal is a in a::"",
  action in [Action::"++++++++++++"],
  resource is a in a::""
) when {
  ((true && (action in (if ((ip("2b2b:2b2b:2b2b:2b2b:2b2b:2b2b:2b2b:2b2d/43")).isIpv4()) then (action["Bsss"]) else (principal["Bsss"])))) && (a::"" in (a::""["Bsss"]))) && (a::"" in (a::""["Bsss"]))
};
