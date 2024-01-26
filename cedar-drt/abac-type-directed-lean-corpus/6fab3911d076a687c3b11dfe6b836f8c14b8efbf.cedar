permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (!((if ((ip("9d9d:9d9d:c960:362b:3436:2536:a036:3536/4ì")).isInRange(ip("0.0.0.1"))) then 0 else 0) <= 0))) && false
};
