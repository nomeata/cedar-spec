permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (!((if ((ip("9d9d:9d9d:9dc9:6036:2b34:3636:a036:3536")).isInRange(ip("ecf2:4500:ece2:f637:36f9:0:459d:9d9d"))) then 0 else 0) <= 0))) && false
};
