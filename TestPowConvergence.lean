import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

open Filter Topology Metric

-- Check what's available for proving existence of N
#check Metric.tendsto_atTop
#check eventually_atTop
#check Filter.Eventually.exists
