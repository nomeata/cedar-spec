forbid(
  principal in rsss::a::"666666666",
  action in [rsss::Action::"action"],
  resource is rsss::a in rsss::a::""
) when {
  true && ((if (principal has "66z\u{12}666") then action else rsss::a::"666666666") has "")
};
