permit(
  principal == a::"j",
  action,
  resource
) when {
  (true && ((a::"j" in (-(""))) in action)) && a::""
};
