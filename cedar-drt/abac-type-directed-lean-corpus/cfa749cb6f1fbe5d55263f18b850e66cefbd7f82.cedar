permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (!((if ((ip("9d9d:9d9d:9dc9:6036:2b34:3636:a036:3536")).isInRange(ip("d3ff:3636:ffff:3636:3636:3636:3636:3601"))) then (if true then 1728053247 else 0) else 2748926567846963394) <= 3891110078048108776))) && false
};
