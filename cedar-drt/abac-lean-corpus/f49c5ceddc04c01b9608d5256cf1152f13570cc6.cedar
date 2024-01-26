forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (if (action * 2139062143) then action else (!""))) && a::""
};
