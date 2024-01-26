permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (!({"": true, "\0\0\0\0": false, "61&": true} has ""))
};
