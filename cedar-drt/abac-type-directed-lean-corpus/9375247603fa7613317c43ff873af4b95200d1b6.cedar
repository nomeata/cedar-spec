permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && (!(90131598130823168 < (if ((ip("5.9.0.0")).isInRange(ip("54.1.64.54"))) then 0 else 0)))
};
